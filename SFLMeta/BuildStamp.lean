import VersoManual
import Std.Time

namespace SFLMeta

/-!
# Build stamp

Every build product says when it was generated: a trailing `--` comment at the
end of each generated `.lean` chapter, and a small grayed-out line at the end of
each HTML page.  Both are rendered from the *same* string, computed once per
`SFLMeta.runVolume` call and threaded to the two emitters, so the stamp on a
chapter's HTML page and the stamp on its `.lean` file read identically and a
reader can tell at a glance that the two came out of one build.

Only the files Verso *generates* are stamped.  The repository sources an
extracted project bundles alongside them (`SFLCompat`, a chapter's
`CustomTactics`, …) are copied verbatim, and staying byte-identical to the
originals is worth more there than a date.
-/

/-- The build stamp for a run starting now.

UTC, to the minute.  The point of the stamp is to let a reader say how old the
copy in front of them is and tell two downloads apart, so it should read the
same to everyone who sees it — which rules out local time, and also means the
seconds would be noise.  Reading the clock in UTC additionally avoids depending
on a time zone database being installed wherever the book is built. -/
def buildStamp : IO String := do
  let now ← Std.Time.Timestamp.now
  let utc :=
    Std.Time.DateTime.ofTimestamp now
      (Std.Time.TimeZone.ZoneRules.ofTimeZone Std.Time.TimeZone.UTC)
  return s!"Built on {utc.format "yyyy-MM-dd HH:mm"} UTC"

/-- `body`, with `stamp` appended as a trailing comment.  Trailing whitespace is
trimmed first so the stamp always sits one blank line below the last line of
code, however the emitter happened to end. -/
def withBuildStamp (stamp body : String) : String :=
  body.trimAsciiEnd.toString ++ "\n\n-- " ++ stamp ++ "\n"

/-- `stamp` as the last line of an HTML page, styled by `.sf-build-stamp` in
`SFLMeta.sfTheme`.  Wired in through `Config.extraContents`, which puts it after
the page contents (just above the navigation buttons). -/
def buildStampHtml (stamp : String) : Verso.Output.Html :=
  open Verso.Output.Html in
  {{<div class="sf-build-stamp">{{stamp}}</div>}}

end SFLMeta
