# Software Foundations in Lean

This repository contains the sources for the _Software Foundations in Lean_ textbook series.

## Status and how to contribute

SF-in-Lean is ready for adventurous alpha-testers!  See
[ALPHATESTERS.md](AlPHATESTERS.md) for instructions on how to get started.

The SF-in-Lean team is also looking for contributors who have time and
interest to make a bigger commitment to the project.  
If you are interested in joining us, please email Benjamin Pierce.

SF-in-Lean is _not_ ready for ordinary readers quite yet. We aim to
have a complete and polished draft of the opening chapters of _Logical
Foundations_ in time for the start of Fall 2026 courses and to finish all of _Logical Foundations_, _Type Systems_, and _Hoare Logic_ by
the end of the semester. 

Translations of further volumes of the original _Software Foundations_ from Rocq to Lean will follow in due course.

## Quick start: Building and viewing the book

To build everything and preview the HTML locally:

    make serve

This builds all volumes in four variants — student / solutions / terse / grading —
into `_out/`, then serves that directory on port 8000.

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

## Repository organization

Each volume has its own top-level directory - `LF`, `HL`, and `TS` - each
of which is paired with a top-level `.lean` file.
Within each directory there are multiple `.lean` files, one per chapter,
written in [Verso](https://verso.lean-lang.org/) format.

Running `make` at the top level produces, for each volume, four
different ready-for-distribution outputs in a temporary top-level
`_out` directory, each with both `.lean` and `.html` variants (in
`_out/<vol>/<variant>/lean/` and `_out/<vol>/<variant>/html-multi/`
respectively).

- **student**   (full prose, solutions elided)
- **solutions** (full prose, solutions shown)
- **terse**     (little prose, no solutions, workinclass elided;
                 for lecturing)
- **grading**   (solutions variant with automated grading support,
                 for instructors)

Students are expected to work through the student `.lean` versions,
filling in the exercises, or to go through the HTML and switch
to the Lean just for exercises. See [ALPHATESTERS.md](ALPHATESTERS.md)
for additional instructions. Instructors are expected to work through
the terse version in class, and use the grading version for grading
homework exercises done by students. We do not keep the solutions
private because GenAI makes this pointless: Anyone can now generate
solutions to any exercise. The solutions aim to show well engineered
proofs.

## Contributing

See [CONTRIBUTING.md](CONTRIBUTING.md) for much more about the
Software Foundations in Lean project — philosophy, conventions,
repo layout, PR workflow, etc.

## License

This project is licensed under the Apache License, Version 2.0. See the
[LICENSE](LICENSE) and [NOTICE](NOTICE) files for details. 

Any contribution you intentionally submit for inclusion in this
work shall be licensed under the same terms, with no additional terms or
conditions.
