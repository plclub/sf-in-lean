# VS Code hints

## Finding what a key is bound to

`Cmd+K Cmd+S` opens the Keyboard Shortcuts editor. Click the **Record Keys**
button — the keyboard icon at the right of the search box — then press the combo
you're curious about. The list filters to every binding that claims it,
including the losers, which is how you spot one binding shadowing another. Click
the X in the search box to clear.

`Cmd+Alt+K` is the keyboard route to the same button, but it only fires while
**focus is in that editor's search box** (`inKeybindings && inKeybindingsSearch`).
Click into the search field first; from the shortcut list below it, the key does
nothing. The button always works, so prefer it.

Filters for that search box:

| Filter | Shows |
|---|---|
| `@source:user` | Only my own bindings |
| `@source:default` | Only VS Code built-ins |
| `@source:extension` | Only bindings contributed by extensions |
| `@command:<id>` | Every binding for one command |
| `@ext:<publisher.name>` | Every binding from one extension |

**When a key appears to do nothing**, Record Keys isn't enough — run
`Developer: Toggle Keyboard Shortcuts Troubleshooting` from the Command Palette.
It logs each keypress and the command actually dispatched to the Output panel
(Window channel), which is the only reliable way to diagnose a chord that never
completes or a `when` clause that isn't matching.

The complete built-in list is at
`Preferences: Open Default Keyboard Shortcuts (JSON)`; my own overrides are at
`Preferences: Open Keyboard Shortcuts (JSON)`.

## My VS Code keybindings

Host `keybindings.json`, macOS.

### Authoring

| Key | Command | Notes |
|---|---|---|
| `ctrl+alt+d` | `editor.action.insertSnippet` | Inserts a `:::dev "Benjamin Pierce (bcpierce00)"` block with the cursor in the body |
| `shift+'` | `editor.action.insertSnippet` | LaTeX only: typing `"` inserts TeX magic quotes ` ``…'' `, wrapping the selection if any |
| `ctrl+'` | `type` | LaTeX only: escape hatch, types a literal `"` |

### Build / run

| Key | Command |
|---|---|
| `ctrl+shift+b` | `latex-workshop.build` |
| `cmd+shift+r` | `workbench.action.tasks.reRunTask` — Emacs `g` in `*compilation*` |
| `ctrl+c ctrl+c` | `extension.coq.stepForward` (when-clause commented out, so global) |

### Navigation

| Key | Command |
|---|---|
| `ctrl+r` | `editor.action.previousMatchFindAction` — Emacs reverse isearch, `editorFocus`. Needs an explicit binding because `ctrl+r` is Open Recent by default on macOS |

### Layout

| Key | Command |
|---|---|
| `ctrl+shift+alt+s` | Save editor group layout |
| `ctrl+shift+alt+d` | Apply editor layout |
| `ctrl+alt+1` | `multiCommand.myLayoutsFocus` |
| `ctrl+alt+2` | `multiCommand.myLayoutsWork` |
| `ctrl+shift+alt+2` | Two columns, 60/40 |
| `ctrl+shift+alt+3` | Three columns, 40/30/30 |

Layout switching uses modified single keystrokes rather than `ctrl+k` chords: a
chord's second key is unmodified, so webview inputs (e.g. the Claude Code chat
box) swallow it as typed text before VS Code sees it.

### Environment

| Key | Command |
|---|---|
| `ctrl+alt+cmd+p` | `remote-containers.reopenInContainer` |
| `cmd+q` | *unbound* (`-workbench.action.quit`) — prevents accidental quit |

### Conflicts and gotchas

- **`ctrl+shift+b`** is free on macOS — the default Run Build Task is
  `cmd+shift+b`, so LaTeX Workshop and the build task coexist. This binding
  *would* shadow Run Build Task on Linux/Windows, so gate it on
  `editorLangId == latex` if this file is ever shared across platforms.
- **`ctrl+c ctrl+c`** is global with its when-clause commented out. Worth
  confirming it doesn't intercept `Ctrl+C` in the integrated terminal.

### Extension dependencies

- `multi-command` — `ctrl+alt+1` / `ctrl+alt+2`
- LaTeX Workshop — `ctrl+shift+b`
- VsCoq — `ctrl+c ctrl+c`
- Dev Containers — `ctrl+alt+cmd+p`

## Claude Code extension bindings

Contributed by `anthropic.claude-code`. These are easy to forget about and are
the first suspects when a `Cmd+Alt+…` or `Cmd+Escape` key "does nothing" —
their effect lands in the Claude Code panel, not the editor.

| Key | Command | When |
|---|---|---|
| `Alt+K` | `claude-vscode.insertAtMention` — Insert @-Mention Reference | `editorTextFocus` |
| `Cmd+Alt+K` | `claude-code.insertAtMentioned` — Insert At-Mentioned | `editorTextFocus` |
| `Cmd+Escape` | Focus / blur the panel (or open the terminal, with `claudeCode.useTerminal`) | varies |
| `Cmd+Shift+Escape` | `claude-vscode.editor.open` | `!config.claudeCode.useTerminal` |
| `Cmd+N` | `claude-vscode.newConversation` | panel focused, gated on `claudeCode.enableNewConversationShortcut` |
| `Cmd+Shift+T` | `claude-vscode.reopenClosedSession` | gated on `claudeCode.enableReopenClosedSessionShortcut` |

Both `Alt+K` and `Cmd+Alt+K` insert an `@`-reference to the current file and
selected line range into the Claude Code prompt — the two commands appear to be
an older and a newer spelling of the same gesture.

## Find / Search (VS Code)

`Cmd+F` opens the **Find widget** in the focused editor — scoped to that one
file, not the workspace. It searches incrementally, shows a `3 of 17` counter,
marks every hit in the scrollbar's overview ruler, seeds itself from the current
selection, and auto-restricts to the selection when that selection spans
multiple lines. `Up`/`Down` in the find box cycles search history. The same
chord opens a *different* find control when the terminal, a webview preview, the
Settings UI, or a list/tree has focus.

### In the widget

| Action | Key |
|---|---|
| Find next / previous | `Enter` / `Shift+Enter` |
| Find next / previous (outside the box) | `Cmd+G` / `Cmd+Shift+G` |
| Toggle Replace input | `Cmd+Alt+F` |
| Replace / Replace all | `Cmd+Shift+1` / `Cmd+Alt+Enter` |
| Match case | `Cmd+Alt+C` |
| Whole word | `Cmd+Alt+W` |
| Regex | `Cmd+Alt+R` |
| Find in selection | `Cmd+Alt+L` |
| Preserve case (replace) | `Cmd+Alt+P` |
| Select all matches | `Alt+Enter` |
| Close | `Escape` |

In regex mode, capture groups work and `$1`/`$2` are available in the replace
box; `\n` and `\t` work in both boxes.

### Related navigation

| Action | Key |
|---|---|
| Search across files | `Cmd+Shift+F` |
| Replace across files | `Cmd+Shift+H` |
| Use selection for find | `Cmd+E` |
| Add next occurrence to multi-cursor | `Cmd+D` |
| Select all occurrences | `Cmd+Shift+L` |
| Go to line | `Ctrl+G` |
| Go to file (quick open) | `Cmd+P` |
| Go to symbol in file | `Cmd+Shift+O` |
| Go to symbol in workspace | `Cmd+T` |

`Cmd+D` is the natural follow-on from a find: each press turns the next match
into an additional cursor, so you can edit all of them at once instead of a
blind Replace All.

## Multiple cursors

### Adding and removing cursors

| Action | Key | Command |
|---|---|---|
| Insert cursor above / below | `Cmd+Alt+Up` / `Cmd+Alt+Down` | `editor.action.insertCursorAbove` / `Below` |
| Insert cursor at click point | `Alt+Click` | — (mouse gesture) |
| Add next occurrence of the selection | `Cmd+D` | `editor.action.addSelectionToNextFindMatch` |
| Skip this occurrence, take the next | `Cmd+K Cmd+D` | `editor.action.moveSelectionToNextFindMatch` |
| Select all occurrences of the selection | `Cmd+Shift+L` | `editor.action.selectHighlights` |
| Select all occurrences of the word under the cursor | `Cmd+F2` | `editor.action.changeAll` |
| Cursor at the end of every selected line | `Shift+Alt+I` | `editor.action.insertCursorAtEndOfEachLineSelected` |
| Select all matches (from the find widget) | `Alt+Enter` | `editor.action.selectAllMatches` |
| Undo the last added cursor | `Cmd+U` | `cursorUndo` |
| Collapse back to one cursor | `Escape` | — |

`Cmd+U` is the one people miss: `Cmd+D` one match too far is recoverable
without starting over.

### The core workflow

Select a token, then `Cmd+D` once per additional occurrence you want, `Cmd+K
Cmd+D` to step over one you don't, and type. This is the incremental
alternative to `Cmd+Shift+L`, which takes every occurrence in the file at once
with no chance to skip. For a whole-file rename in a `.lean` file prefer F2
(Rename Symbol), which is scope-aware; multi-cursor is for the cases the
language server won't handle — prose, comments, table rows, repeated markup.

### Column (box) selection

| Action | Key |
|---|---|
| Extend box selection | `Shift+Alt+Cmd+Up` / `Down` / `Left` / `Right` |
| Box-select with the mouse | `Shift+Alt+drag` |
| Persistent column-selection mode | Command Palette: `Toggle Column Selection Mode` |

### Editing commands that respect every cursor

| Action | Key |
|---|---|
| Toggle line comment | `Cmd+/` |
| Delete line | `Cmd+Shift+K` |
| Move line up / down | `Alt+Up` / `Alt+Down` |
| Copy line up / down | `Shift+Alt+Up` / `Shift+Alt+Down` |
| Word-wise motion | `Alt+Left` / `Alt+Right` |
| Line start / end | `Cmd+Left` / `Cmd+Right` |

### Settings

- `editor.multiCursorModifier` — default `alt` on macOS: `Alt+Click` adds a
  cursor, `Cmd+Click` is Go to Definition. **Keep the default** for Lean work,
  where Go to Definition is the more frequent gesture. Setting it to `ctrlCmd`
  swaps the two (Sublime style).
- `editor.multiCursorPaste` — `spread` (default) pastes one clipboard line per
  cursor when the counts match; `full` pastes the whole clipboard at every
  cursor.
- `editor.multiCursorLimit` — 10000 by default; lower it if a stray
  `Cmd+Shift+L` on a common token ever locks up the editor.

### Interaction with my own bindings

None of the multi-cursor defaults collide with the current `keybindings.json`,
and none collide with the Bookmarks extension's `Cmd+Alt+J/K/L`.

## Bookmarks

### Built in — no extension needed

| Action | Key | Command |
|---|---|---|
| Go back | `Ctrl+-` | `workbench.action.navigateBack` |
| Go forward | `Ctrl+Shift+-` | `workbench.action.navigateForward` |
| Last edit location | `Cmd+K Cmd+Q` | `workbench.action.navigateToLastEditLocation` |
| Go to line | `Ctrl+G` | `workbench.action.gotoLine` |
| Go to symbol in file | `Cmd+Shift+O` | `workbench.action.gotoSymbol` |

VS Code's navigation stack is the closest built-in analogue to bookmarks: it
records jump origins automatically, so back/forward retraces where you have
been rather than where you deliberately marked.

### Bookmarks extension (`alefragnani.Bookmarks`)

| Action | Key |
|---|---|
| Toggle bookmark on current line | `Cmd+Alt+K` |
| Jump to next bookmark | `Cmd+Alt+L` |
| Jump to previous bookmark | `Cmd+Alt+J` |

**Dev Containers:** nothing to do — Bookmarks runs as a *UI* extension on the
Mac and serves container windows from there. In the Extensions view it sits
under **Local — Installed** with an activation-time badge and *no* "Install in
Dev Container" button, which is the tell: VS Code offers that button only for
extensions that must run remotely (C/C++, the Lean 4 server, and so on). An
activation badge means it is live in the current window.

That distinction is worth remembering in general — a *workspace* extension
really does have to be installed container-side, and the fix there is the
"Install in Dev Container" button, or the host setting
`dev.containers.defaultExtensions` to do it for every container automatically.

Further commands (list bookmarks, clear all, select lines between bookmarks) are
available from the Command Palette under `Bookmarks:` but have no stable default
binding — check the Keyboard Shortcuts UI after installing.

**Two live collisions**, so rebind rather than take the defaults:

* `Cmd+Alt+K` (toggle bookmark) is already `claude-code.insertAtMentioned`,
  with the same `editorTextFocus` when-clause. Extension-vs-extension conflicts
  resolve by registration order — don't rely on it.
* `Cmd+Alt+L` (jump to next) overlaps VS Code's built-in Find-in-selection
  toggle.

Moving Bookmarks to free keys settles both:

```json
{ "key": "cmd+alt+k", "command": "-bookmarks.toggle" },
{ "key": "cmd+alt+l", "command": "-bookmarks.jumpToNext" },
{ "key": "cmd+alt+j", "command": "-bookmarks.jumpToPrevious" },
{ "key": "ctrl+alt+k", "command": "bookmarks.toggle",         "when": "editorTextFocus" },
{ "key": "ctrl+alt+n", "command": "bookmarks.jumpToNext",     "when": "editorTextFocus" },
{ "key": "ctrl+alt+p", "command": "bookmarks.jumpToPrevious", "when": "editorTextFocus" }
```

## Build / make-like commands

### Built in

| Action | Key | Command |
|---|---|---|
| Run Build Task | `Cmd+Shift+B` | `workbench.action.tasks.build` |
| Run Task | *unbound* | `workbench.action.tasks.runTask` |
| Rerun Last Task | *unbound* | `workbench.action.tasks.reRunTask` |
| Run Test Task | *unbound* | `workbench.action.tasks.test` |
| Terminate Task | *unbound* | `workbench.action.tasks.terminate` |
| Restart Running Task | *unbound* | `workbench.action.tasks.restartTask` |
| Show Running Tasks | *unbound* | `workbench.action.tasks.showTasks` |

Only Run Build Task has a default binding; everything else is Command Palette
only until bound.

### Navigating build errors — the `next-error` analogue

| Action | Key | Command |
|---|---|---|
| Next problem, across files | `F8` | `editor.action.marker.nextInFiles` |
| Previous problem, across files | `Shift+F8` | `editor.action.marker.prevInFiles` |
| Next problem, current file | `Alt+F8` | `editor.action.marker.next` |
| Previous problem, current file | `Shift+Alt+F8` | `editor.action.marker.prev` |
| Toggle Problems panel | `Cmd+Shift+M` | `workbench.actions.view.problems` |

`F8` is the direct counterpart to Emacs `next-error` in `*compilation*`.

### In the sf-in-lean repo

`.vscode/tasks.json` defines one task, `make`, marked as the default build
task — so `Cmd+Shift+B` runs bare `make`, which is `default: all` → `lf hl ts`,
i.e. **all three volumes in all four variants**. That is the full build, not a
quick check.

Useful Makefile targets to wire to lighter tasks:

| Target | Effect |
|---|---|
| `make <vol>-build` | `lake build sfl-<vol>` only — no rendering |
| `make <vol>-student` | Student variant for one volume |
| `make <vol>-solutions` | Solutions variant |
| `make <vol>-terse` | Terse/lecture variant |
| `make <vol>-grading` | Grading variant |
| `make <vol>` | All four variants for that volume |
| `make student` / `solutions` / `terse` / `grading` | One variant across all volumes |
| `make style` | Style-guide conformance checks |
| `make style-checklist` | Print the judgement-based audit checklist |
| `make grading-check` | `scripts/grading_check.py` over LF/HL/TS |
| `make serve` | Build all, then serve `_out/` on :8000 |
| `make release ARGS="--volumes lf"` | Package a local release |
| `make clean` | `lake clean` + remove `_out/` |

`<vol>` is `lf`, `hl`, or `ts`. For a single chapter, `lake build LF.Basics` is
faster than any make target.

### Interaction with my own bindings

- `Cmd+Shift+B` still runs the default build task; the LaTeX Workshop binding
  sits on `ctrl+shift+b` and doesn't interfere on macOS.
- `Cmd+Shift+R` is already bound to `workbench.action.tasks.reRunTask`.
- Worth binding: `workbench.action.tasks.runTask` and
  `workbench.action.tasks.terminate`, both unbound by default.
  
