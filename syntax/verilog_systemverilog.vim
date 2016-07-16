" Vim syntax file
" Language:	SystemVerilog (superset extension of Verilog)

" Extends Verilog syntax
" Requires $VIMRUNTIME/syntax/verilog.vim to exist

" For version 5.x: Clear all syntax items
" For version 6.x: Quit when a syntax file was already loaded
if version < 600
   syntax clear
elseif exists("b:current_syntax")
   finish
endif

" Override 'iskeyword'
if version >= 600
   setlocal iskeyword=@,48-57,_,192-255
else
   set iskeyword=@,48-57,_,192-255
endif

" Store cpoptions
let oldcpo=&cpoptions
set cpo-=C

syn sync lines=1000

"##########################################################
"       SystemVerilog Syntax
"##########################################################

syn keyword verilogStatement   always and assign automatic buf
syn keyword verilogStatement   bufif0 bufif1 cell cmos
syn keyword verilogStatement   config deassign defparam design
syn keyword verilogStatement   disable edge endconfig
syn keyword verilogStatement   endgenerate endmodule
syn keyword verilogStatement   endprimitive endtable
syn keyword verilogStatement   event force fork join
syn keyword verilogStatement   join_any join_none forkjoin
syn keyword verilogStatement   generate genvar highz0 highz1 ifnone
syn keyword verilogStatement   incdir include initial inout input
syn keyword verilogStatement   instance integer large liblist
syn keyword verilogStatement   library localparam macromodule medium
syn keyword verilogStatement   module nand negedge nmos nor
syn keyword verilogStatement   noshowcancelled not notif0 notif1 or
syn keyword verilogStatement   output parameter pmos posedge primitive
syn keyword verilogStatement   pull0 pull1 pulldown pullup
syn keyword verilogStatement   pulsestyle_onevent pulsestyle_ondetect
syn keyword verilogStatement   rcmos real realtime reg release
syn keyword verilogStatement   rnmos rpmos rtran rtranif0 rtranif1
syn keyword verilogStatement   scalared showcancelled signed small
syn keyword verilogStatement   specparam strong0 strong1
syn keyword verilogStatement   supply0 supply1 table time tran
syn keyword verilogStatement   tranif0 tranif1 tri tri0 tri1 triand
syn keyword verilogStatement   trior trireg unsigned use vectored wait
syn keyword verilogStatement   wand weak0 weak1 wire wor xnor xor

syn keyword verilogStatement   always_comb always_ff always_latch
syn keyword verilogStatement   checker endchecker
syn keyword verilogStatement   virtual local const protected
syn keyword verilogStatement   package endpackage
syn keyword verilogStatement   rand randc constraint randomize
syn keyword verilogStatement   with inside dist
syn keyword verilogStatement   randcase
syn keyword verilogStatement   randsequence
syn keyword verilogStatement   get_randstate set_randstate
syn keyword verilogStatement   srandom
syn keyword verilogStatement   logic bit byte time
syn keyword verilogStatement   int longint shortint
syn keyword verilogStatement   struct packed
syn keyword verilogStatement   final
syn keyword verilogStatement   import export
syn keyword verilogStatement   context pure
syn keyword verilogStatement   void shortreal chandle string
syn keyword verilogStatement   modport
syn keyword verilogStatement   cover coverpoint
syn keyword verilogStatement   program endprogram
syn keyword verilogStatement   bins binsof illegal_bins ignore_bins
syn keyword verilogStatement   alias matches solve static assert
syn keyword verilogStatement   assume before expect bind
syn keyword verilogStatement   extends null tagged extern this
syn keyword verilogStatement   first_match throughout timeprecision
syn keyword verilogStatement   timeunit priority type union
syn keyword verilogStatement   uwire var cross ref wait_order intersect
syn keyword verilogStatement   wildcard within
syn keyword verilogStatement   triggered
syn keyword verilogStatement   std
syn keyword verilogStatement   accept_on eventually global implements implies
syn keyword verilogStatement   interconnect let nettype nexttime reject_on restrict soft
syn keyword verilogStatement   s_always s_eventually s_nexttime s_until s_until_with
syn keyword verilogStatement   strong sync_accept_on sync_reject_on unique unique0
syn keyword verilogStatement   until until_with untyped weak

syn keyword verilogTypeDef     typedef enum

syn keyword verilogConditional iff
syn keyword verilogConditional if else case casex casez default endcase

syn keyword verilogRepeat      forever repeat while for
syn keyword verilogRepeat      return break continue
syn keyword verilogRepeat      do while foreach

syn match   verilogGlobal      "`[a-zA-Z_][a-zA-Z0-9_$]\+"
syn match   verilogGlobal      "$[a-zA-Z0-9_$]\+"

syn match   verilogConstant    "\<[A-Z][A-Z0-9_$]\+\>"

syn match   verilogNumber      "\(\d\+\)\?'[sS]\?[bB]\s*[0-1_xXzZ?]\+"
syn match   verilogNumber      "\(\d\+\)\?'[sS]\?[oO]\s*[0-7_xXzZ?]\+"
syn match   verilogNumber      "\(\d\+\)\?'[sS]\?[dD]\s*[0-9_xXzZ?]\+"
syn match   verilogNumber      "\(\d\+\)\?'[sS]\?[hH]\s*[0-9a-fA-F_xXzZ?]\+"
syn match   verilogNumber      "\<[+-]\?[0-9_]\+\(\.[0-9_]*\)\?\(e[0-9_]*\)\?\>"
syn match   verilogNumber      "\<\d[0-9_]*\(\.[0-9_]\+\)\=\([fpnum]\)\=s\>"
syn keyword verilogNumber      1step

syn keyword verilogTodo        contained TODO FIXME

syn match   verilogOperator    "[&|~><!)(*#%@+/=?:;}{,.\^\-\[\]]"

syn region  verilogComment     start="/\*" end="\*/" contains=verilogTodo,@Spell
syn match   verilogComment     "//.*" contains=verilogTodo,@Spell

syn region  verilogString      start=+"+ skip=+\\"+ end=+"+ contains=verilogEscape,@Spell
syn match   verilogEscape      +\\[nt"\\]+ contained
syn match   verilogEscape      "\\\o\o\=\o\=" contained

" Directives
syn match   verilogDirective   "//\s*synopsys\>.*$"
syn region  verilogDirective   start="/\*\s*synopsys\>" end="\*/"
syn region  verilogDirective   start="//\s*synopsys \z(\w*\)begin\>" end="//\s*synopsys \z1end\>"

syn match   verilogDirective   "//\s*\$s\>.*$"
syn region  verilogDirective   start="/\*\s*\$s\>" end="\*/"
syn region  verilogDirective   start="//\s*\$s dc_script_begin\>" end="//\s*\$s dc_script_end\>"

syn keyword verilogMethod      new
if v:version >= 704
    syn match   verilogMethod  "\(^\s\+\.\)\@30<!\<\w\+\ze("
else
    syn match   verilogMethod  "\(^\s\+\.\)\@<!\<\w\+\ze("
endif

syn match   verilogLabel       "\<\k\+\>\ze\s*:\s*\<\(assert\|assume\|cover\(point\)\?\|cross\)\>"
if v:version >= 704
    syn match   verilogLabel   "\(\<begin\>\s*:\s*\)\@20<=\<\k\+\>"
else
    syn match   verilogLabel   "\(\<begin\>\s*:\s*\)\@<=\<\k\+\>"
endif

syn keyword verilogObject      super
syn match   verilogObject      "\<\w\+\ze\(::\|\.\)" contains=verilogNumber

" Only enable folding if verilog_syntax_fold_lst is defined
let s:verilog_syntax_fold=verilog_systemverilog#VariableGetValue("verilog_syntax_fold_lst")

if index(s:verilog_syntax_fold, "task") >= 0 || index(s:verilog_syntax_fold, "all") >= 0
    syn region  verilogFold
        \ matchgroup=verilogStatement
        \ start="\(\(\(extern\s\+\(\(pure\s\+\)\?virtual\s\+\)\?\)\|\(\pure\s\+virtual\s\+\)\)\(\(static\|protected\|local\)\s\+\)\?\)\@<!\<task\>"
        \ end="\<endtask\>"
        \ transparent
        \ keepend
        \ fold
    syn match   verilogStatement "\(\(\(extern\s\+\(\(pure\s\+\)\?virtual\s\+\)\?\)\|\(\pure\s\+virtual\s\+\)\)\(\(static\|protected\|local\)\s\+\)\?\)\@<=\<task\>"
else
    syn keyword verilogStatement  task endtask
endif
if index(s:verilog_syntax_fold, "function") >= 0 || index(s:verilog_syntax_fold, "all") >= 0
    syn region  verilogFold
        \ matchgroup=verilogStatement
        \ start="\(\(\(extern\s\+\(\(pure\s\+\)\?virtual\s\+\)\?\)\|\(\pure\s\+virtual\s\+\)\)\(\(static\|protected\|local\)\s\+\)\?\)\@<!\<function\>"
        \ end="\<endfunction\>"
        \ transparent
        \ keepend
        \ fold
    syn match   verilogStatement "\(\(\(extern\s\+\(\(pure\s\+\)\?virtual\s\+\)\?\)\|\(\pure\s\+virtual\s\+\)\)\(\(static\|protected\|local\)\s\+\)\?\)\@<=\<function\>"
else
    syn keyword verilogStatement  function endfunction
endif
if index(s:verilog_syntax_fold, "class") >= 0 || index(s:verilog_syntax_fold, "all") >= 0
    syn region  verilogFold
        \ matchgroup=verilogStatement
        \ start="\(typedef\s\+\)\@<!\<\(interface\s\+\)\?class\>"
        \ end="\<endclass\>"
        \ transparent
        \ fold
    syn match   verilogStatement "\(typedef\s\+\)\@<=\<class\>"
else
    syn keyword verilogStatement class endclass
endif
if index(s:verilog_syntax_fold, "interface") >= 0 || index(s:verilog_syntax_fold, "all") >= 0
    syn region  verilogFold
        \ matchgroup=verilogStatement
        \ start="\<interface\>\(\s\+class\)\@!"
        \ end="\<endinterface\>"
        \ transparent
        \ keepend
        \ fold
else
    syn keyword verilogStatement interface endinterface
endif
if index(s:verilog_syntax_fold, "clocking") >= 0 || index(s:verilog_syntax_fold, "all") >= 0
    syn region  verilogFold
        \ matchgroup=verilogStatement
        \ start="\<clocking\>"
        \ end="\<endclocking\>"
        \ transparent
        \ keepend
        \ fold
else
    syn keyword verilogStatement clocking endclocking
endif
if index(s:verilog_syntax_fold, "covergroup") >= 0 || index(s:verilog_syntax_fold, "all") >= 0
    syn region  verilogFold
        \ matchgroup=verilogStatement
        \ start="\<covergroup\>"
        \ end="\<endgroup\>"
        \ transparent
        \ keepend
        \ fold
else
    syn keyword verilogStatement  covergroup endgroup
endif
if index(s:verilog_syntax_fold, "sequence") >= 0 || index(s:verilog_syntax_fold, "all") >= 0
    syn region  verilogFold
        \ matchgroup=verilogStatement
        \ start="\<sequence\>"
        \ end="\<endsequence\>"
        \ transparent
        \ keepend
        \ fold
else
    syn keyword verilogStatement  sequence endsequence
endif
if index(s:verilog_syntax_fold, "property") >= 0 || index(s:verilog_syntax_fold, "all") >= 0
    syn region  verilogFold
        \ matchgroup=verilogStatement
        \ start="\<property\>"
        \ end="\<endproperty\>"
        \ transparent
        \ keepend
        \ fold
else
    syn keyword verilogStatement  property endproperty
endif
if index(s:verilog_syntax_fold, "specify") >= 0 || index(s:verilog_syntax_fold, "all") >= 0
    syn region  verilogFold
        \ matchgroup=verilogStatement
        \ start="\<specify\>"
        \ end="\<endspecify\>"
        \ transparent
        \ keepend
        \ fold
else
    syn keyword verilogStatement  specify endspecify
endif
if index(s:verilog_syntax_fold, "block_nested") >= 0 || index(s:verilog_syntax_fold, "block_named") >= 0
    syn region verilogFoldBlockContainer
        \ start="\<begin\>"
        \ end="\<end\>"
        \ skip="/[*/].*"
        \ transparent
        \ keepend extend
        \ containedin=ALLBUT,verilogComment
        \ contains=verilogComment,verilogFold,verilogBlock
    if index(s:verilog_syntax_fold, "block_nested") >= 0
        syn region verilogFold
            \ start="\<begin\>"
            \ end="\<end\>"me=s-1
            \ transparent
            \ fold
            \ contained containedin=verilogFoldBlockContainer
            \ contains=TOP
        syn match verilogStatement "\<begin\|end\>"
    else "block_named
        syn region verilogBlock
            \ start="\<begin\>"
            \ end="\<end\>"
            \ transparent
            \ contained containedin=verilogFoldBlockContainer
            \ contains=TOP,verilogFold
        syn region verilogFold
            \ start="\<begin\>\ze\s*:\s*\z(\w\+\)"
            \ end="\<end\>"me=s-1
            \ transparent
            \ fold
            \ contained containedin=verilogBlock
            \ contains=TOP
        syn match verilogStatement "\<begin\|end\>"
    endif
elseif index(s:verilog_syntax_fold, "block") >= 0 || index(s:verilog_syntax_fold, "all") >= 0
    syn region  verilogFold
        \ matchgroup=verilogStatement
        \ start="\<begin\>"
        \ end="\<end\>"
        \ transparent
        \ fold
else
    syn keyword verilogStatement  begin end
endif
if index(s:verilog_syntax_fold, "define") >= 0 || index(s:verilog_syntax_fold, "all") >= 0
    syn region verilogFoldIfContainer
        \ start="`ifn\?def\>"
        \ end="`endif\>"
        \ skip="/[*/].*"
        \ transparent
        \ keepend extend
        \ containedin=ALLBUT,verilogComment
        \ contains=NONE
    syn region verilogFoldIf
        \ start="`ifn\?def\>"
        \ end="^\s*`els\(e\|if\)\>"ms=s-1,me=s-1
        \ fold transparent
        \ keepend
        \ contained containedin=verilogFoldIfContainer
        \ nextgroup=verilogFoldElseIf,verilogFoldElse
        \ contains=TOP
    syn region verilogFoldElseIf
        \ start="`els\(e\|if\)\>"
        \ end="^\s*`els\(e\|if\)\>"ms=s-1,me=s-1
        \ fold transparent
        \ keepend
        \ contained containedin=verilogFoldIfContainer
        \ nextgroup=verilogFoldElseIf,verilogFoldElse
        \ contains=TOP
    syn region verilogFoldElse
        \ start="`else\>"
        \ end="`endif\>"
        \ fold transparent
        \ keepend
        \ contained containedin=verilogFoldIfContainer
        \ contains=TOP
endif
if index(s:verilog_syntax_fold, "instance") >= 0 || index(s:verilog_syntax_fold, "all") >= 0
    syn region verilogFold
        \ start="^\s*\w\+\(\s*#\s*(\|\s\+\w\+\s*(\)\(.*)\s*\w\+\s*;\)\@!"
        \ end=")\s*;"
        \ transparent
        \ fold
        \ keepend
endif

" Expand verilogComment
if len(s:verilog_syntax_fold) > 0
    syn clear   verilogComment
    syn match   verilogComment  "//.*"                      contains=verilogTodo,@Spell
    if index(s:verilog_syntax_fold, "comment") >= 0 || index(s:verilog_syntax_fold, "all") >= 0
        syn region  verilogComment  start="/\*"     end="\*/"   contains=verilogTodo,@Spell                     keepend fold
    else
        syn region  verilogComment  start="/\*"     end="\*/"   contains=verilogTodo,@Spell                     keepend
    endif
endif

"Modify the following as needed.  The trade-off is performance versus
"functionality.
syn sync minlines=50

" Define the default highlighting.
" For version 5.7 and earlier: only when not done already
" For version 5.8 and later: only when an item doesn't have highlighting yet
if version >= 508 || !exists("did_verilog_syn_inits")
   if version < 508
      let did_verilog_syn_inits = 1
      command -nargs=+ HiLink hi link <args>
   else
      command -nargs=+ HiLink hi def link <args>
   endif

   " The default highlighting.
   HiLink verilogCharacter       Character
   HiLink verilogConditional     Conditional
   HiLink verilogRepeat          Repeat
   HiLink verilogString          String
   HiLink verilogTodo            Todo
   HiLink verilogComment         Comment
   HiLink verilogConstant        Constant
   HiLink verilogLabel           Tag
   HiLink verilogNumber          Number
   HiLink verilogOperator        Special
   HiLink verilogStatement       Statement
   HiLink verilogGlobal          Define
   HiLink verilogDirective       SpecialComment
   HiLink verilogEscape          Special
   HiLink verilogMethod          Function
   HiLink verilogTypeDef         TypeDef
   HiLink verilogObject          Type

   delcommand HiLink
endif

let b:current_syntax = "verilog_systemverilog"

" Restore cpoptions
let &cpoptions=oldcpo

" vim: sts=4 sw=4
