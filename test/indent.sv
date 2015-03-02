// Code based on: https://github.com/vhda/verilog_systemverilog.vim/issues/2
class z;

    // this is a comment
    // -----------------
    typedef struct {
        real a;
        int b;
        int c;
        real d; } ts;

    ts s[];

    // if there are
    // more comments
    typedef struct {
        real a;
        int b;
        int c;
        real d;
    } ts2;

    ts2 t[];

    int unsigned cnt=0;

    function new();
        super.new();
    endfunction;

    // Code from: https://github.com/vhda/verilog_systemverilog.vim/issues/4
    task run_phase(uvm_phase phase);

        assert(my_seq.randomize());
        my_seq.start(low_sequencer_h);

        assert(my_seq.randomize() with {Nr==6;});
        my_seq.start(low_sequencer_h);

        assert(my_seq.randomize() with
            {Nr==6; Time==8;});
        my_seq.start(low_sequencer_h);

        assert(
            my_seq.randomize() with
            {Nr==6; Time==8;}
        );
        my_seq.start(low_sequencer_h);

        // Code from: https://github.com/vhda/verilog_systemverilog.vim/issues/5
        fork
            begin : isolating_thread
                do_something();
            end : isolating_thread
        join

    endtask

    // Code from: https://github.com/vhda/verilog_systemverilog.vim/issues/7
    task run_phase2(uvm_phase phase);
        assert(out>0) else $warning("xxx");
        assert(out>0) else $warning("xxx");
        foreach(out[i]) begin
            out[i]=new;
        end
    endtask

    // Oter tests
    task fork_test;
        fork
            do_something1();
            do_something2();
        join_none
        do_something3();
    endtask

    function old_style_function_with_var(
        input a
    );
    reg test;
    begin
        do_something1();
        do_something2();
        begin
            do_something3();
        end
    end
    endfunction

    function old_style_function_without_var(
        input a
    );
    begin
        do_something1();
        do_something2();
        begin
            do_something3();
        end
    end
    endfunction

    function old_style_function_one_line_with_var(input a);
        reg x;
    begin
        do_something1();
        do_something2();
        begin
            do_something3();
        end
    end
    endfunction

    function old_style_function_one_line_without_var(input a);
    begin
        do_something1();
        do_something2();
        begin
            do_something3();
        end
    end
    endfunction

endclass

// vim: set sts=4 sw=4 nofen:
