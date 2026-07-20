# Software Foundations in Lean

This repository contains the work-in-progress sources for [Software
Foundations](https://softwarefoundations.cis.upenn.edu/) in Lean.

## Status

SF-in-Lean is _not_ ready for ordinary readers yet.  We'll make a
posting on the Lean Zulip when we've got something suitable for public
consumption. We aim to have a complete and polished draft of most
chapters of _Logical Foundations_ and _Programming Language
Foundations_ in time for Fall 2026 courses. 

If you would like to be notified when chapters are ready for
alpha-testing, please email [Benjamin
Pierce](mailto:bcpierce@cis.upenn.edu).

We are also not set up yet to consider PRs from outside the
translation team.  If you are interested in joining the team, please
email Benjamin Pierce and we can discuss.

## Quick start: building and viewing the book

To build everything and preview the HTML locally:

    make serve

then visit <http://localhost:8000>.  (This builds all volumes in all
three variants — student / solutions / terse — into `_out/`, then
serves that directory on port 8000.)

To rebuild just one volume, use its make target and then serve `_out/`:

    make lf          # or: hl, ts
    make lf-student  # just one variant: -student, -solutions, -terse
    python3 -m http.server 8000 -d _out/

The HTML for a given volume and variant lands in
`_out/<vol>/<variant>/html-multi/`, one page per chapter.  (There is no
per-chapter build target; a volume is the smallest unit.)

The first build compiles the Lean toolchain's worth of dependencies and
takes a while; later builds are incremental.

## Orientation

For everything else — repo layout, conventions, PR workflow — see
[CONTRIBUTING.md](CONTRIBUTING.md).

## License

This project is licensed under the Apache License, Version 2.0. See the
[LICENSE](LICENSE) and [NOTICE](NOTICE) files for details. 
Any contribution you intentionally submit for inclusion in this
work shall be licensed under the same terms, with no additional terms or
conditions.
