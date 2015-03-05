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
        // End of copied code

    endtask
    // End of copied code

    // Code from: https://github.com/vhda/verilog_systemverilog.vim/issues/7
    task run_phase2(uvm_phase phase);
        assert(out>0) else $warning("xxx");
        assert(out>0) else $warning("xxx");
        foreach(out[i]) begin
            out[i]=new;
        end
    endtask
    // End of copied code

    // Code from: https://github.com/vhda/verilog_systemverilog.vim/issues/12
    task my_seq::body();
        `uvm_info({get_type_name(),"::body"}, "something" ,UVM_HIGH)
        req = my_seq_item_REQ::type_id::create("req");
    endtask
    // End of copied code

    // Oter tests
    task fork_test;
        fork
            do_something1();
            do_something2();
        join_none // {}
        do_something3();
    endtask

    task while_one_line;
        while (1)
            do_something();
    endtask

    task while_block;
        while (1)
        begin
            do_something();
        end
    endtask

    task while_block2;
        while (1) begin
            do_something();
        end
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

module m (
    portA,
    portB
);

device d0 (
    .port (port[1]),
    .port2(), // comment
    .portA(port[2])
);

// Code from: https://github.com/vhda/verilog_systemverilog.vim/issues/6
device d1 (
    .port (port[1]),
    // .port2(), // comment
    .*
);
// End of copied code

device d1 (
    .port (port[1]),
    // .port1(), comment
    /**/.port2(), // comment
    /*.port3(), */   
    // .port4(), comment
    .portA(port[2])
);

`ifdef V95
    device d2 ( out, portA, portB );
`elsif V2K
    device d2 ( .out(out), .* );
`endif
`ifndef SWAP
    device d3 ( .out(out), .* );
`else
    device d3 ( .out(out), .portA(portB), .portB(portA) );
`elsif 

endmodule

// vim: set sts=4 sw=4 nofen:
