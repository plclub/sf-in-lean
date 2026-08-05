import SFLMeta

open Verso.Genre Manual
open SFLMeta

#doc (Manual) "Preface" =>
%%%
tag := "Preface"
htmlSplit := .never
file := some "Preface"
%%%

:::dev
The real preface is being written on the `add-preface-postscript` branch
(issue #165); this minimal page exists to exercise the shared bibliography
(`SFLMeta.Bib`, issue #147) with a live citation.
:::

For a classic introduction to interactive theorem proving in the tradition
this book builds on, see {citet Bib.bertot2004}[].
