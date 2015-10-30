function f;                                                   //<1>
begin                                                         //<2>
                                                              //<2>
end                                                           //<2>
endfunction : f                                               //<1>
                                                              //<0>
task t;                                                       //<1>
                                                              //<1>
begin                                                         //<2>
    begin                                                     //<3>
    end                                                       //<3>
end                                                           //<2>
                                                              //<1>
endtask : t                                                   //<1>
                                                              //<0>
/*                                                            //<1>
*                                                             //<1>
* function in_comment;                                        //<1>
*                                                             //<1>
* endfunction                                                 //<1>
*                                                             //<1>
*/                                                            //<1>
                                                              //<0>
extern function ext_func (x, y);                              //<0>
                                                              //<0>
extern static function ext_static_func (x, y);                //<0>
                                                              //<0>
extern protected function ext_protected_func (x, y);          //<0>
                                                              //<0>
extern local function ext_local_func (x, y);                  //<0>
                                                              //<0>
extern pure virtual function ext_pure_virt_func (x);          //<0>
                                                              //<0>
pure virtual function pure_virt_func (x);                     //<0>
                                                              //<0>
pure virtual static function pure_virt_static_func (x);       //<0>
                                                              //<0>
pure virtual protected function pure_virt_protected_func (x); //<0>
                                                              //<0>
pure virtual local function pure_virt_local_func (x);         //<0>
                                                              //<0>
                                                              //<0>
extern task ext_task (x, y);                                  //<0>
                                                              //<0>
extern static task ext_static_task (x, y);                    //<0>
                                                              //<0>
extern protected task ext_protected_task (x, y);              //<0>
                                                              //<0>
extern local task ext_local_task (x, y);                      //<0>
                                                              //<0>
extern pure virtual task ext_pure_virt_task (x);              //<0>
                                                              //<0>
pure virtual task pure_virt_task (x);                         //<0>
                                                              //<0>
pure virtual static task pure_virt_static_task (x);           //<0>
                                                              //<0>
pure virtual protected task pure_virt_protected_task (x);     //<0>
                                                              //<0>
pure virtual local task pure_virt_local_task (x);             //<0>
                                                              //<0>
/**                                                           //<1>
* Static function                                             //<1>
*/                                                            //<1>
static function f1;                                           //<1>
endfunction                                                   //<1>
                                                              //<0>
specify                                                       //<1>
                                                              //<1>
endspecify                                                    //<1>
                                                              //<0>
covergroup cov;                                               //<1>
                                                              //<1>
endgroup                                                      //<1>
                                                              //<0>
property prop;                                                //<1>
endproperty                                                   //<1>
                                                              //<0>
sequence                                                      //<1>
endsequence                                                   //<1>
                                                              //<0>
// Classes                                                    //<0>
class class_a;                                                //<1>
                                                              //<1>
endclass : class_a                                            //<1>
                                                              //<0>
class class_b;                                                //<1>
  class class_b1;                                             //<2>
                                                              //<2>
  endclass : class_b1                                         //<2>
                                                              //<1>
  class class_b2;                                             //<2>
                                                              //<2>
  endclass : class_b2                                         //<2>
endclass : class_b                                            //<1>
                                                              //<0>
interface a;                                                  //<1>
                                                              //<1>
  interface class b;                                          //<2>
  endclass : b                                                //<2>
                                                              //<1>
  clocking cb @ (posedge Clk);                                //<2>
  endclocking : cb                                            //<2>
                                                              //<1>
endinterface : a                                              //<1>
                                                              //<0>
`ifdef A                                                      //<1>
reg test;                                                     //<1>
                                                              //<1>
//  `ifdef A_1                                                //<1>
//                                                            //<1>
//  `else                                                     //<1>
//                                                            //<1>
//  `endif                                                    //<1>
                                                              //<1>
`else                                                         //<1>
                                                              //<1>
`endif                                                        //<1>
                                                              //<0>
`ifndef B                                                     //<1>
                                                              //<1>
`elsif C                                                      //<1>
                                                              //<1>
`elsif D                                                      //<1>
                                                              //<1>
`else                                                         //<1>
                                                              //<1>
`endif                                                        //<1>
                                                              //<0>
`ifdef E                                                      //<1>
                                                              //<1>
  `ifndef E_1                                                 //<2>
                                                              //<2>
  `else                                                       //<2>
                                                              //<2>
  `endif                                                      //<2>
                                                              //<1>
`endif                                                        //<1>
                                                              //<0>
`ifdef A                                                      //<1>
                                                              //<1>
  `ifdef B                                                    //<2>
                                                              //<2>
  `else                                                       //<2>
                                                              //<2>
  `endif                                                      //<2>
                                                              //<1>
`elsif C                                                      //<1>
                                                              //<1>
`else                                                         //<1>
                                                              //<1>
`endif                                                        //<1>
                                                              //<0>
                                                              //<0>
/*                                                            //<1>
  `ifdef X                                                    //<1>
                                                              //<1>
  `else                                                       //<1>
                                                              //<1>
  `endif                                                      //<1>
*/                                                            //<1>

