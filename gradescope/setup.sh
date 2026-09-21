#!/usr/bin/env bash
# Claude-generated (see CLAUDE.md, "Marking AI-generated material").
#
# Gradescope build-time setup. Runs once, as root, with the zip already
# unpacked at /autograder/source.
#
# Everything expensive belongs here rather than in run_autograder: the Lean
# toolchain, the grader binaries, and a compiled workspace. Grading a
# submission then recompiles one file and needs no network.
set -euo pipefail

SRC=/autograder/source
. "${SRC}/config.env"

LANDRUN_VERSION=v0.1.17
GO_VERSION=go1.27.0

export DEBIAN_FRONTEND=noninteractive
apt-get update
apt-get install -y --no-install-recommends ca-certificates curl git python3 build-essential
rm -rf /var/lib/apt/lists/*

export ELAN_HOME=/opt/elan
export PATH=/opt/elan/bin:${PATH}
curl -fsSL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
  | sh -s -- -y --default-toolchain "${LEAN_TOOLCHAIN}" --no-modify-path

# A throwaway Lake project whose only job is to produce the two binaries.
mkdir -p /opt/grader/bin /opt/grader/tools
cd /opt/grader/tools
cat > lakefile.toml <<TOML
name = "sfl-grader-tools"
version = "0.1.0"

[[require]]
name = "comparator-autograder"
git = "${COMPARATOR_AUTOGRADER_URL}"
rev = "${COMPARATOR_AUTOGRADER_REV}"
TOML
printf '%s' "${LEAN_TOOLCHAIN}" > lean-toolchain
lake build lean4export comparatorautograder
cp .lake/packages/comparator-autograder/.lake/build/bin/comparatorautograder /opt/grader/bin/
cp .lake/packages/lean4export/.lake/build/bin/lean4export                    /opt/grader/bin/
cp .lake/packages/comparator/scripts/fake-landrun.sh                         /opt/grader/bin/
chmod +x /opt/grader/bin/*
cd / && rm -rf /opt/grader/tools

# The two trees ship already namespaced, so this is a copy.
mkdir -p /opt/grader/workspace
cp -R "${SRC}/context/Challenge" "${SRC}/context/Solution" \
      "${SRC}/context/SFLCompat" "${SRC}/context/SFLCompat.lean" /opt/grader/workspace/
cp "${SRC}/context/lakefile.toml" "${SRC}/context/lean-toolchain" /opt/grader/workspace/
cp "${SRC}/grade.py" /opt/grader/grade.py

cd /opt/grader/workspace
# Only what this assignment needs: its graded chapters and, through their
# imports, the solved dependencies staged alongside them.
TARGETS=""
for c in $(printf '%s' "${CHAPTER}" | tr ',' ' '); do
  TARGETS="${TARGETS} Challenge.${VOLUME}.${c} Solution.${VOLUME}.${c}"
done
lake build ${TARGETS}

# ── sandbox ──────────────────────────────────────────────────────────────────
# The comparator runs lake and lean4export through $COMPARATOR_LANDRUN. The
# vendored fake-landrun.sh confines nothing; real landrun confines them with
# Linux Landlock (kernel 5.13+), which matters because student Lean code runs
# arbitrary code at elaboration time.
#
# As of 2026-08, Gradescope's runners report Landlock ABI v0 -- no support at
# all -- so the probe below rejects landrun and grading runs unsandboxed. No
# landrun version changes that; it is the kernel. The build is kept anyway so
# the sandbox turns itself on if that ever changes; --no-sandbox skips it.
#
# Built from source, not downloaded: the published release binaries link against
# glibc 2.38 and Ubuntu 22.04 has 2.35. CGO_ENABLED=0 sidesteps libc entirely --
# landrun's only cgo-touching dependency, libcap/psx, has a pure-Go fallback.
cp /opt/grader/bin/fake-landrun.sh /opt/grader/bin/landrun     # fallback
case "$(uname -m)" in
  x86_64)        LR_ARCH=amd64 ;;
  aarch64|arm64) LR_ARCH=arm64 ;;
  *)             LR_ARCH= ;;
esac

# Landlock needs kernel 5.13+. Gradescope's runners are Amazon Linux 2 on 4.14,
# where landrun can only ever report ABI v0, so building it there costs a Go
# toolchain download for a binary that cannot work. Check first.
KVER=$(uname -r | cut -d- -f1)
KMAJ=${KVER%%.*}
KMIN=$(printf '%s' "${KVER#*.}" | cut -d. -f1)
if [ "${KMAJ}" -gt 5 ] 2>/dev/null || { [ "${KMAJ}" -eq 5 ] && [ "${KMIN}" -ge 13 ]; } 2>/dev/null
then LANDLOCK_POSSIBLE=yes; else LANDLOCK_POSSIBLE=no; fi

if [ -n "${SFL_LANDRUN:-}" ]; then
  echo "=== sandbox: disabled by config (SFL_LANDRUN=${SFL_LANDRUN}) ==="
elif [ "${LANDLOCK_POSSIBLE}" = no ]; then
  echo "=== sandbox: kernel $(uname -r) predates Landlock (needs 5.13+);" \
       "skipping the landrun build -- GRADING WILL RUN UNSANDBOXED ===" >&2
elif [ -n "${LR_ARCH}" ] \
   && curl -fsSL --retry 3 "https://go.dev/dl/${GO_VERSION}.linux-${LR_ARCH}.tar.gz" \
        | tar -C /usr/local -xz \
   && CGO_ENABLED=0 GOBIN=/opt/grader GOFLAGS=-trimpath \
        /usr/local/go/bin/go install "github.com/zouuup/landrun/cmd/landrun@${LANDRUN_VERSION}"
then
  # Two separate probes, so the log says which one failed. Running is not
  # enough: --best-effort degrades to no enforcement when the kernel lacks
  # Landlock, and the build succeeds either way -- so the second probe checks
  # that a write outside .lake is actually refused.
  LOG=/tmp/landrun-probe.log
  PROBE=/opt/grader/workspace/Challenge/.landrun-write-probe
  rm -f "${PROBE}"
  echo "kernel $(uname -r); lsm: $(cat /sys/kernel/security/lsm 2>/dev/null || echo unknown)"

  landrun_run() {
    /opt/grader/landrun --best-effort --ro / --rw /dev -ldd -add-exec \
      --env PATH --env HOME --env LEAN_ABORT_ON_PANIC \
      --ro /opt/grader/workspace --rwx /opt/grader/workspace/.lake \
      --rox "$(lean --print-prefix)" -- "$@"
  }

  if ! landrun_run lake build ${TARGETS} > "${LOG}" 2>&1; then
    echo "=== WARNING: landrun could not run the build -- GRADING WILL RUN UNSANDBOXED ===" >&2
    head -20 "${LOG}" >&2
  elif landrun_run touch "${PROBE}" >> "${LOG}" 2>&1; then
    echo "=== WARNING: landrun ran, but a write to Challenge/ was NOT blocked ===" >&2
    echo "=== Landlock is not enforcing here; GRADING WILL RUN UNSANDBOXED ===" >&2
    # --best-effort swallows the reason. Ask again without it, purely so the
    # build log records *why* the kernel would not give us a ruleset.
    echo "--- why (landrun without --best-effort) ---" >&2
    /opt/grader/landrun --ro / -- /bin/true 2>&1 | head -5 >&2 || true
    head -20 "${LOG}" >&2
  else
    mv /opt/grader/landrun /opt/grader/bin/landrun
    echo "=== sandbox: landrun ${LANDRUN_VERSION} (Landlock enforcing) ==="
  fi
  rm -f "${PROBE}"
else
  echo "=== WARNING: could not build landrun -- GRADING WILL RUN UNSANDBOXED ===" >&2
fi
rm -rf /usr/local/go /root/go /opt/grader/landrun   # toolchain and module cache

# What a submission replaces, and what run_autograder restores before each run.
cp -R Solution /opt/grader/pristine
