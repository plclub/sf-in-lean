# SF-in-Lean: Instructions for Alpha-Testers

- fork the [repo](https://github.com/plclub/sf-in-lean) into your own github account
- clone your copy onto your local machine
- tell your clone where the original repo lives, so you can pick up our changes
  later:
  ```
  git remote add upstream https://github.com/plclub/sf-in-lean.git
  ```
- type `make student` in the top-level directory
- open `_out/lf/student/html-multi/index.html`
- follow the installation instructions in the `Preface` to install
  VSCode and Lean if necessary
- start reading!

If you see an opportunity for a clear improvement, make a fix directly in the appropriate `.lean`
file in the `LF`, `HL`, or `TS` subdirectory.

If you want to leave a comment, add it to the `.lean` file like this:
```
    :::dev "Your Real Name (@your_github_handle)"
    ... Your suggestions ...
    :::
```    

Make a github PR for any changes to a given chapter once you finish reading it.  (We prefer chapter-level PRs so they don't get too large or too stale.)

When you open the PR, leave the **"Allow edits by maintainers"** box checked (it
is checked by default).  It lets anyone with write access to the SF-in-Lean repo
push a small fixup directly to your branch — a typo, a build fix — instead of
asking you to round-trip it, which will get your contributions merged faster.

We are actively working on all the chapters, so if you're reading a
chapter over a long period, make sure to pull from the source repo often.
Note that a plain `git pull` only gets you your *own* fork, which never
updates itself — you have to ask for ours by name:

```
git fetch upstream
git merge upstream/main
```
