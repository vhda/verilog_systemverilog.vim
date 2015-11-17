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


" Read in Verilog syntax files
if version < 600
   so syntax/verilog.vim
else
   runtime! syntax/verilog.vim
endif

" Store cpoptions
let oldcpo=&cpoptions
set cpo-=C

syn sync lines=1000

"##########################################################
"       SystemVerilog Syntax
"##########################################################

syn clear verilogLabel
syn clear verilogStatement
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

syn keyword verilogRepeat      return break continue
syn keyword verilogRepeat      do while foreach

syn match   verilogGlobal      "`begin_\w\+"
syn match   verilogGlobal      "`end_\w\+"
syn match   verilogGlobal      "`remove_\w\+"
syn match   verilogGlobal      "`restore_\w\+"

syn match   verilogGlobal      "`[a-zA-Z0-9_]\+\>"

syn match   verilogNumber      "\<\d[0-9_]*\(\.\?[0-9_]\+\)\=\([fpnum]\)\=s\>"
syn keyword verilogNumber      1step

syn keyword verilogMethod      new
syn match   verilogMethod      "\(\s\+\.\)\@<!\<\w\+\ze("

syn match   verilogLabel       "\<\k\+\>\ze\s*:\s*\<assert\>"
if v:version >= 704
    syn match   verilogLabel   "\(\<begin\>\s*:\s*\)\@20<=\<\k\+\>"
else
    syn match   verilogLabel   "\(\<begin\>\s*:\s*\)\@<=\<\k\+\>"
endif

syn keyword verilogObject      super
syn match   verilogObject      "\<\w\+\ze\(::\|\.\)" contains=verilogNumber

" Only enable folding if g:verilog_syntax_fold is defined
if exists("g:verilog_syntax_fold")
    let s:verilog_syntax_fold=split(g:verilog_syntax_fold, ",")
else
    let s:verilog_syntax_fold=[]
endif

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
    syn match   veirlogStatement "\(typedef\s\+\)\@<=\<class\>"
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
if index(s:verilog_syntax_fold, "block_nested") >= 0
    syn region verilogFoldBlockContainer
        \ start="\<begin\>"
        \ end="\<end\>"
        \ skip="/[*/].*"
        \ transparent
        \ keepend extend
        \ containedin=ALLBUT,verilogComment
        \ contains=NONE
    syn region  verilogFold
        \ start="\<begin\>"
        \ end="\<end\>"me=s-1
        \ transparent
        \ fold
        \ contained containedin=verilogFoldBlockContainer
        \ contains=TOP
    syn match verilogLabel "\<begin\|end\>"
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
    " The above syntax regions start/end matches will disable the respective
    " verilogGlobal keywords. This syntax match fixes that:
    syn match verilogGlobal "\<`\(ifn\?def\|e\(els\(e\|if\)\)\|ndif\)\>"
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

   " Override default verilogLabel link
   highlight! default link verilogLabel Tag

   " The default highlighting.
   HiLink verilogMethod          Function
   HiLink verilogTypeDef         TypeDef
   HiLink verilogObject          Type

   delcommand HiLink
endif

let b:current_syntax = "verilog_systemverilog"

" Restore cpoptions
let &cpoptions=oldcpo

" vim: sts=4 sw=4
