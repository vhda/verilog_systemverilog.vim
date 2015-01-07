#Vim Syntax Addon for Verilog and SystemVerilog

## About

Based on script originally found at:

http://www.vim.org/scripts/script.php?script_id=1586

## Features

Besides some bug corrections, the following features were added to this set of scripts:

* Omni-completion.
* Configurable syntax folding.
* Updated matchit configurations to properly support Verilog 2001 and SystemVerilog.
* Automatically enabled for the following file extensions: .v.vh.sv.svi.svh

### Omni-Completion

The omni-completion functionality requires a tags file generated with
[exuberant-ctags][e] using the `--extra=+q` argument to enable class qualified
tags. No other command or tools was tested, but should work seemingly as long as
it able to generate standard class qualified tags.
For more information on using omni-completion please check the vim man page for
[`i_CTRL-X_CTRL-O`][vim-omni].

Currently supported contexts:

1. Module instantiation port names.
2. Function/task arguments.
3. Object methods and attrtibutes.

The required option [`omnifunc`][vim-omnifunc] is automatically defined for the
supported file extensions.

__Note__: Proper SystemVerilog tag generation requires development version of
[exuberant-ctags][c].

### Syntax folding

To enable syntax folding set the following option:

`set foldmethod=syntax`

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

* __b:g:verilog\_dont\_deindent\_eos__ - Keep last `)` of module port declaration de-indented.

### Syntax options

* __g:verilog\_syntax\_fold__ - Enable verilog syntax folding.
  Comma separated list containing one or more of the following values:
  * function
  * task
  * specify
  * covergroup
  * sequence
  * property
  * all (enables all above options)
  Set to an empty string to disable syntax folding.

### Debug options

* __b:verilog\_indent\_verbose__ - Verbose indenting (uses `echom`).
* __b:verilog\_omni\_verbose__ - Verbose omni-completion (uses `echom`).

## Other Verilog/SystemVerilog addons for Vim

### Matchit

This addon allows using `%` to jump between matching keywords as Vim already
does for matchin parentheses/brackets. Many syntax files include the definition
of the matching keyword pairs for their supported languages.

Since it is already included in all Vim installations and the addon can be
easily loaded by adding the following line to `.vimrc`:

```
runtime macros/matchit.vim
```

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
[vim-omni]:     http://vimdoc.sourceforge.net/htmldoc/insert.html#i_CTRL-X_CTRL-O
[vim-omnifunc]: http://vimdoc.sourceforge.net/htmldoc/options.html#'omnifunc'


<!-- Other links:
https://github.com/nachumk/systemverilog.vim
-->
