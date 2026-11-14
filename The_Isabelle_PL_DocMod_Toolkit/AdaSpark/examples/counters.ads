--  A global counter: abstract state and dependency contracts.

package Counters
  with SPARK_Mode,
       Abstract_State => Counter_State,
       Initializes    => Counter_State
is
   Limit : constant := 1_000;

   function Value return Natural
     with Global => (Input => Counter_State);

   procedure Increment
     with Global  => (In_Out => Counter_State),
          Depends => (Counter_State => Counter_State),
          Pre     => Value < Limit,
          Post    => Value = Value'Old + 1;

   procedure Reset
     with Global => (Output => Counter_State),
          Post   => Value = 0;

end Counters;
