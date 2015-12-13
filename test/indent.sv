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

        // Code from: https://github.com/vhda/verilog_systemverilog.vim/issues/15
        assert(out>0) else $warning("xxx");
        $display("Hi");

        assert(out>0)
        else $warning("xxx");
        $display("Hi");

        assert(out>0) else $warning("xxx");
        $display("Hi");
        $display("Hi");
        // End of copied code

        assert(out>0)
        else
            $warning("xxx");
        $display("Hi");

        if (1 > 0) $display("1 > 0");
        else $display("1 < 0");
        $display();

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

    /*
    *
    *
    *
    */

    // Code from: https://github.com/vhda/verilog_systemverilog.vim/issues/12
    task my_seq::body();
        `uvm_info({get_type_name(),"::body"}, "something" ,UVM_HIGH)
        req = my_seq_item_REQ::type_id::create("req");
    endtask
    // End of copied code

    // Code from: https://github.com/vhda/verilog_systemverilog.vim/issues/14
    pure virtual function void a(input int unsigned N, ref t Data);
    pure virtual function void b(input int unsigned N, ref t Data);
    pure virtual function void c(input int unsigned N, ref t Data);
    // End of copied code

    // Code from: https://github.com/vhda/verilog_systemverilog.vim/issues/17
    function void sink_driver::build_phase(uvm_phase phase);
        if (!uvm_config_db #(sink_agent_config)::get(this, "", "sink_agent_config", m_cfg) )
            `uvm_fatal("CONFIG_LOAD", "Cannot get() configuration sink_agent_config from uvm_config_db. Have you set() it?")
        // OK to do this herE>
        foreach(rand_bool_gen[ch]) begin
            rand_bool_gen[ch]=new();
        end
    endfunction
    // End of copied code

    // Code from: https://github.com/vhda/verilog_systemverilog.vim/issues/41
    `uvm_info("TAG", "message", UVM_MEDIUM)

    if (condition)
        `uvm_info("TAG", "message1", UVM_MEDIUM)
    else
        `uvm_info("TAG", "message2", UVM_NONE)
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

    virtual task virtual_task;
        while (1) begin
            do_something();
        end
    endtask

    virtual function virtual_function;
        while (1) begin
            do_something();
        end
    endfunction

    //function old_style_function_with_var(
    //    input a
    //);
    //reg test;
    //begin 
    //    do_something1();
    //    do_something2();
    //    begin
    //        do_something3();
    //    end
    //end
    //endfunction

    //function old_style_function_without_var(
    //    input a
    //);
    //begin
    //    do_something1();
    //    do_something2();
    //    begin
    //        do_something3();
    //    end
    //end
    //endfunction

    //function old_style_function_one_line_with_var(input a);
    //    reg x;
    //begin
    //    do_something1();
    //    do_something2();
    //    begin
    //        do_something3();
    //    end
    //end
    //endfunction

    //function old_style_function_one_line_without_var(input a);
    //begin
    //    do_something1();
    //    do_something2();
    //    begin
    //        do_something3();
    //    end
    //end
    //endfunction

endclass

// Code from: https://github.com/vhda/verilog_systemverilog.vim/issues/14
virtual class base;

    extern function void x(input int unsigned N, ref t Data);
    extern function void y(input int unsigned N, ref t Data);

    pure virtual function void a(input int unsigned N, ref t Data);
    pure virtual function void b(input int unsigned N, ref t Data);
    pure virtual function void c(input int unsigned N, ref t Data);

endclass;
// End of copied code

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
`endif

endmodule

class a;
    function void hello();
        foreach (element[i])
            if (hi)
                if (hi) /* comment */ begin /* comment */
                    if (hi) begin
                        foreach (element[i])
                            if (condition0) 
                                if (condition1) begin
                                    var0 <= 0;
                                end
                                else begin
                                    if (1) begin
                                        var1 <= 1;
                                        something();
                                        if (1)
                                            if (1) begin
                                                something();
                                            end
                                            else
                                                if (1)
                                                    if (1) begin
                                                        if (1)
                                                            something();
                                                        else begin
                                                            something();
                                                        end
                                                    end
                                                    else if (1)
                                                        something();

                                        if (1)
                                            something();

                                        something();
                                        something();
                                    end
                                end
                        deindent_x2_please();
                        dont_deindent_please();
                    end
                    deindent_please();
                end
        deindent_please();
        dont_deindent_please();
    endfunction : hello
endclass : a
module a;
(
    input clk,
    output x
);

always @ (posedge clk)
begin
end

always 
    x <= 1;

always
begin
    x <= 1;
    statement();
end

always //
begin
    x <= 1;
    statement();
end

label : always //
    x <= 1;

always @ (posedge clk) //
    x <= 1;

always @ (posedge clk)
    x <= 1;

always_ff // begin
    x <= 1;

always_comb
    x <= 1;

label : always_ff begin
    begin
        x <= 1;
        statement();
    end
end

always_ff
begin
    x <= 1;
    statement();
    foreach (object[i])
        statement();
end

// always_ff
// begin
//     x <= 1;
// end

endmodule

if (condition) begin
    something();
end
else
    `macro_call()

always : label
    `macro_call()

begin
    begin
    end // always
    `dont_indent()
    dont_deindent();

    begin
    end // foreach()
    dont_indent();
    dont_deindent();

    begin
    end /* while() */
    dont_indent();
    dont_deindent();
end

class a extends b;
    function void hello();
        if (1)
            fork
                something();
                something();
                begin
                    something();
                end
                begin
                    fork
                        if (1)
                            if (1)
                                if (1) begin
                                    something();
                                end
                        something();
                    join
                end
                if (1)
                    foreach (objects[i])
                        if (1)
                            if (1) begin
                                something();
                            end
                something();
            join_none
    endfunction : hello
endclass : a



// vim: set sts=4 sw=4 nofen:
