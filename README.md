# Software Foundations in Lean

This repository contains the work-in-progress sources for [Software
Foundations](https://softwarefoundations.cis.upenn.edu/) in Lean.

## Status and how to contribute

SF-in-Lean _is_ ready for adventurous alpha-testers.  See
ALPHATESTERS.md for instructions on how to get started.

The SF-in-Lean team is also looking for contributors who have time and
interest to make a more significant commitment tothe project.  
If you are interested in joining us, please email Benjamin Pierce.

SF-in-Lean is _not_ ready for ordinary readers quite yet. We aim to
have a complete and polished draft of the opening chapters of _Logical
Foundations_ in time for the start of Fall 2026 courses and to finish
both _Logical Foundations_ and _Programming Language Foundations_ by
the end of the year. 

## Quick start: Building and viewing the book

To build everything and preview the HTML locally:

    make serve

(This builds all volumes in all three variants — student / solutions / terse —
into `_out/`, then serves that directory on port 8000.)  
Then open `http://localhost:8000` in a web browser.

To rebuild just one volume, use its make target and then serve `_out/`:

    make lf          # or: hl, ts
    make lf-student  # or lf-solutions, lf-terse, etc.
    python3 -m http.server 8000 -d _out/

The HTML for a given volume and variant lands in
`_out/<vol>/<variant>/html-multi/`, one page per chapter.  (There is no
per-chapter build target: a whole volume is the smallest unit.)

The first build compiles the whole Lean toolchain's dependencies and
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
