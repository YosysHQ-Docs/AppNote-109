`default_nettype none
module liveness
  (input bit clk, rstn,
   input bit  start,
   output bit done);

   typedef enum logic [1:0] {idle, decrypt, validate_key, inform_result} states_t;
   states_t ps;

   default clocking fpv_clk @(posedge clk); endclocking

   // Drive the reset sequence
   init0: assume property($fell(rstn) |=> ps == idle);
   init1: assume property($rose(rstn) |=> rstn);

   // Drive outputs
   ap_done: assume property(ps == inform_result |=> done);
   
   // Write the state machine transitions as assumptions
   state0: assume property(disable iff(!rstn)
			   start && ps == idle |=> ps == decrypt);
   
   state1: assume property(disable iff(!rstn)
			   ps == decrypt |=> ps == validate_key);

`ifdef _ERR_
   // Deadlock due unreachable state
   state2: assume property(disable iff(!rstn)
			   ps == validate_key |=> ps == inform_result);
`else
   state2: assume property(disable iff(!rstn)
			   ps == validate_key |=> ps == <state>); // correct state
`endif
   state3: assume property(disable iff(!rstn)
			   ps == inform_result |=> ps == idle);
   
   // A weak unbounded property that cant catch the deadlock
   ap_deadlock: assert property(disable iff(!rstn)
				ps == idle |-> ##[1:$] ps == inform_result);

   // A liveness property to check for FSM deadlocks better than ap_deadlock
   ap_deadlock_2: assert property(disable iff(!rstn)
				  ps == idle |=> s_eventually ps == inform_result);
   // Fairness constrain
`ifdef 0
   ap_fairness: assume property(disable iff(!rstn)
   				!start |=> s_eventually start);
`endif
endmodule // liveness
