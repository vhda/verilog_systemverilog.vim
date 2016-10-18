function! TestFold(...)
    let fail = 0
    let fail_lines = ''
    let linenr = 0
    if exists("a:1")
        let index = a:1
    else
        let index = 0
    endif
    while linenr < line("$")
        let linenr += 1
        let line = getline(linenr)
        let levels = substitute(line, '.\{-}<\(\d*\)>', '\1::', 'g')
        let levels_list = split(levels, '::')
        " Skip commented out lines
        if line =~ '^\/\/'
            continue
        " Check if requested index is NOT available in the levels list
        elseif index < 0 || (index >= len(levels_list))
            echo 'Invalid line format:'
            echo line
            return 1
        else
            " Store expected indent level
            let level_expected=levels_list[index]
        endif
        " Check indent level
        let level = foldlevel(linenr)
        if (level != level_expected)
            let fail = 1
            echo "Error: level=" . level . " level_expected=" . level_expected . " >>>>" . line
            if (fail_lines == '')
                let fail_lines = linenr
            else
                let fail_lines = fail_lines.','.linenr
            endif
        endif
    endwhile

    if (fail == 1)
        echo 'Fold test failed:'
        echo 'g:verilog_syntax_fold: ' . g:verilog_syntax_fold
        echo fail_lines
        return 1
    else
        echo 'Fold test passed'
        return 0
    endif

endfunction

function! TestIndent()
    let fail = 0
    let fail_lines = ''
    let linenr = 0
    while linenr < line("$")
        let linenr += 1
        let line = getline(linenr)
        let ind1 = indent(linenr)
        execute 'normal! '.linenr.'gg=='
        let ind2 = indent(linenr)
        if ind1 != ind2
            let fail = 1
            if (fail_lines == '')
                let fail_lines = linenr
            else
                let fail_lines = fail_lines.','.linenr
            endif
        endif
    endwhile

    if (fail == 1)
        echo 'Indent test failed:'
        echo fail_lines
        return 1
    else
        echo 'Indent test passed'
        return 0
    endif

endfunction

function! TestEfm(tool, mode, search_uvm)
    let expected_errors   = 0
    let expected_warnings = 0
    let expected_lints    = 0
    let uvm_expected_errors   = 0
    let uvm_expected_warnings = 0
    let uvm_expected_lints    = 0

    " Re-read test file
    silent view test/errorformat.txt

    " Obtain tool configuration from file
    let config_found = 0
    let linenr = 0
    while linenr < line("$")
        let linenr += 1
        let line = getline(linenr)
        " Tool config line
        let tool_config = matchlist(line, '^### *' . tolower(a:tool) . ' E=\(\d\+\), *W=\(\d\+\)\(, *L=\(\d\+\)\)\?')
        if len(tool_config) != 0
            let expected_errors = tool_config[1]
            if a:mode == 1
                let expected_warnings = tool_config[2]
            else
                let expected_warnings = 0
            endif
            if a:mode <= 2
                let expected_lints = tool_config[4]
            else
                let expected_lints = 0
            endif
            let config_found = 1
            if !a:search_uvm
                break
            endif
        endif
        " UVM config line
        let uvm_config = matchlist(line, '^### *UVM E=\(\d\+\), *W=\(\d\+\)\(, *L=\(\d\+\)\)\?')
        if len(uvm_config) != 0
            let uvm_expected_errors = uvm_config[1]
            if len(uvm_config) > 1
                let uvm_expected_warnings = uvm_config[2]
            endif
            if len(uvm_config) > 3
                let uvm_expected_lints = uvm_config[4]
            endif
            let uvm_config_found = 1
            if config_found
                break
            endif
        endif
    endwhile

    if !config_found
        echo 'Test for tool ' . tolower(a:tool) . ' was not found'
        return 1
    endif

    " Calculate total expected errors
    if a:search_uvm
        let expected_errors   += uvm_expected_errors
        let expected_warnings += uvm_expected_warnings
        let expected_lints    += uvm_expected_lints
    endif

    " Setup 'errorformat' and 'makeprg'
    call verilog_systemverilog#VerilogErrorFormat(a:tool, a:mode)
    setlocal makeprg=cat\ %

    " Populate quickfix window
    silent! make!
    redraw

    " Check results
    let errors = 0
    let warnings = 0
    let lints = 0
    let qf_list = getqflist()
    for qf_entry in qf_list
        " Only check valid entries
        if qf_entry.valid != 0
            " Consider Fatal and matches without type as errors
            if qf_entry.type == 'E' ||
                        \ qf_entry.type == 'F' ||
                        \ qf_entry.type == ''
                let errors += 1
            endif
            if qf_entry.type == 'W'
                let warnings += 1
            endif
            " Consider Info as lint
            if qf_entry.type == 'L' ||
                        \ qf_entry.type == 'I'
                let lints += 1
            endif
        endif
    endfor
    echo 'Results:'
    echo ' Expected errors = ' . expected_errors . ', errors found = ' . errors
    echo ' Expected warnings = ' . expected_warnings . ', warnings found = ' . warnings
    echo ' Expected lints = ' . expected_lints . ', lints found = ' . lints
    echo ' errorformat = ' . &errorformat
    echo 'Quickfix contents:'
    for qf_entry in qf_list
        echo qf_entry
    endfor
    if errors == expected_errors && warnings == expected_warnings && lints == expected_lints
        echo 'Error format test passed'
        return 0
    else
        echo 'Error format test failed:'
        return 1
    endif
endfunction

" vi: set expandtab softtabstop=4 shiftwidth=4:
