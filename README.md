#Vim Syntax Plugin for Verilog and SystemVerilog

## About

Based on script originally found at:

http://www.vim.org/scripts/script.php?script_id=1586

[comment]: <http://> "_ stop highlighting the underscore from the link above"

#__NOTICE: Repository history has been rewritten__

## Features

Besides some bug corrections, the following features were added to this set of scripts:

* Omni completion.
* Configurable syntax folding.
* Updated matchit configurations to properly support Verilog 2001 and SystemVerilog.
* Error format definitions for common Verilog tools.
* Automatically enabled for the following file extensions: .v.vh.sv.svi.svh

### Omni Completion

This plugin implements an omni completion function that will offer completion
suggestions depending on the current context. This will only work if a `.`
character is found in the keyword behind the cursor. At the moment the following
contexts are supported:

1. Module instantiation port names.
2. Function/task arguments.
3. Object methods and attrtibutes.

In order to use omni completion a tags file must be generated using the
following arguments:

* `--extra=+q` - Enable hierarchy qualified tags extraction.
* `--fields=+i` - Enable class inheritance extraction.
* `-n` - (Optional) Use line number instead of Ex: patterns to identify
  declaration.

No tool alternative to [exuberant-ctags][e] was tested, but any tool should work
seemingly as long as it is able to generate a standard class qualified tags file.
For more information on using omni completion please check the vim man page for
[`i_CTRL-X_CTRL-O`][vim-omni] (the required option [`omnifunc`][vim-omnifunc] is
automatically defined for the supported file extensions).

__Note__: Proper SystemVerilog tag generation requires development version of
[exuberant-ctags][c].

### Syntax folding

To enable syntax folding set the following option:

`set foldmethod=syntax`

### Verilog Compilation and Error format

This plugin includes the [errorformat][vim-errorformat] configurations for
the following Verilog tools:

* Synopsys VCS (`vcs`)
* Mentor Modelsim (`msim`)
* Icarus Verilog (`iverilog`)
* GPL Cver (`cver`)
* Synopsys Leda (`leda`)

The command `VerilogErrorFormat` allows the interactive selection of these
configurations. In some cases it is also possible to ignore _lint_ and/or
_warning_ level messages.

A specific tool can be directly selected calling this command with some
arguments. Below is an example for `VCS`:

```
VerilogErrorFormat vcs 2
```

In this example the second argument disables the detection of _lint_ messages.
This argument can take the following values:

1. All messages are detected.
2. Ignore _lint_ messages.
3. Ignore _lint_ and _warning_ messages.

After the [errorformat][vim-errorformat] has been so defined, it is only a
matter of setting [makeprg][vim-makeprg] and run `:make` to call the tool of
choice and vim will automatically detect errors, open the required file(s) and
place the cursor on the error position. To navigate the error list use the
commands `:cnext` and `:cprevious`.

For more information check the help page for the [quickfix][vim-quickfix]
vim feature.

## Installation

### Using [Vundle][v]

1. Add the following to your `vimrc`:

 `Plugin 'vhda/verilog_systemverilog.vim'`
2. Run:

 `vim +PluginInstall +qall`

### Using [Pathogen][p]

1. `cd ~/.vim/bundle`
2. `git clone https://github.com/vhda/verilog_systemverilog.vim`

## Configuration

### Indent options

* __b:verilog\_indent\_width__ - Use this variable to override the option `&shiftwidth`.

* __b:verilog\_indent\_modules__ - Indent code after module declaration.

* __b:g:verilog\_dont\_deindent\_eos__ - Keep last `)` of module port declaration indented.

### Syntax options

* __g:verilog\_syntax\_fold__ - Enable verilog syntax folding.
  Comma separated list containing one or more of the following values:
  * function
  * task
  * specify
  * covergroup
  * sequence
  * property
  * specify
  * block (`begin`, `end`)
  * comment (`/*..*/`)
  * define (`` `ifdef ``,`` `ifndef ``, `` `elsif ``, `` `else ``, `` `endif ``)
  * all (enables all above options)

  Set to an empty string to disable syntax folding.

### Debug options

* __b:verilog\_indent\_verbose__ - Verbose indenting (uses [`echom`][vim-echom]).
* __b:verilog\_omni\_verbose__ - Verbose omni completion (uses [`echom`][vim-echom]).

## Other Vim addons helpful for Verilog/SystemVerilog

### Matchit

This addon allows using `%` to jump between matching keywords as Vim already
does for matching parentheses/brackets. Many syntax files include the definition
of the matching keyword pairs for their supported languages.

Since it is already included in all Vim installations and the addon can be
easily loaded by adding the following line to `.vimrc`:

```
runtime macros/matchit.vim
```

### Highlight Matchit

The [hl_matchit.vim][hl_matchit] addon complements Matchit by automatically
underlining matching words, similarly as Vim already does for
parentheses/brackets.

### Supertab

[Supertab][supertab] configures the <kbd>tab</kbd> key to perform insert
completion. To take full advantage of the omni completion functionality the
following configuration should be used:

`let g:SuperTabDefaultCompletionType = "context"`

When this is done [Supertab][supertab] will choose the most appropriate type of
completion to use depending on the current context.

### Tagbar

[Tagbar][t] allows browsing all variable, functions, tasks, etc within a file in
a nice hierarchical view. SystemVerilog language and Verilog/SystemVerilog
hierarchical browsing are only supported when used together with the development
version of [exuberant-ctags][c].

Use the following configuration:

```
let g:tagbar_type_verilog_systemverilog = {
        \ 'ctagstype'   : 'SystemVerilog',
        \ 'kinds'       : [
            \ 'b:blocks:1:1',
            \ 'c:constants:1:0',
            \ 'e:events:1:0',
            \ 'f:functions:1:1',
            \ 'm:modules:0:1',
            \ 'n:nets:1:0',
            \ 'p:ports:1:0',
            \ 'r:registers:1:0',
            \ 't:tasks:1:1',
            \ 'A:assertions:1:1',
            \ 'C:classes:0:1',
            \ 'V:covergroups:0:1',
            \ 'I:interfaces:0:1',
            \ 'M:modport:0:1',
            \ 'K:packages:0:1',
            \ 'P:programs:0:1',
            \ 'R:properties:0:1',
            \ 'T:typedefs:0:1'
        \ ],
        \ 'sro'         : '.',
        \ 'kind2scope'  : {
            \ 'm' : 'module',
            \ 'b' : 'block',
            \ 't' : 'task',
            \ 'f' : 'function',
            \ 'C' : 'class',
            \ 'V' : 'covergroup',
            \ 'I' : 'interface',
            \ 'K' : 'package',
            \ 'P' : 'program',
            \ 'R' : 'property'
        \ },
    \ }
```


[c]: https://github.com/exuberant-ctags/ctags
[p]: https://github.com/tpope/vim-pathogen
[v]: https://github.com/gmarik/vundle
[e]: http://ctags.sourceforge.net/
[t]: http://majutsushi.github.io/tagbar/
[hl_matchit]:   https://github.com/vimtaku/hl_matchit.vim
[supertab]:     https://github.com/ervandew/supertab
[vim-omni]:     http://vimdoc.sourceforge.net/htmldoc/insert.html#i_CTRL-X_CTRL-O
[vim-omnifunc]: http://vimdoc.sourceforge.net/htmldoc/options.html#'omnifunc'
[vim-echom]:    http://vimdoc.sourceforge.net/htmldoc/eval.html#:echom
[vim-errorformat]: http://vimdoc.sourceforge.net/htmldoc/options.html#'errorformat'
[vim-makeprg]:  http://vimdoc.sourceforge.net/htmldoc/options.html#'makeprg'
[vim-quickfix]: http://vimdoc.sourceforge.net/htmldoc/quickfix.html


<!-- Other links:
https://github.com/nachumk/systemverilog.vim
-->
