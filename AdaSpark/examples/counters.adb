package body Counters
  with SPARK_Mode,
       Refined_State => (Counter_State => Count)
is
   Count : Natural := 0;

   function Value return Natural is (Count)
     with Refined_Global => (Input => Count);

   procedure Increment is
   begin
      Count := Count + 1;
   end Increment;

   procedure Reset is
   begin
      Count := 0;
   end Reset;

end Counters;
