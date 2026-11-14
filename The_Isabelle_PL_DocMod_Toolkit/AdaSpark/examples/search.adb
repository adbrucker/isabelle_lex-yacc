package body Search
  with SPARK_Mode
is

   procedure Find (A : Int_Array; Key : Integer; Pos : out Natural) is
      Low  : Natural := A'First;
      High : Natural := A'Last;
      Mid  : Natural;
   begin
      Pos := 0;
      while Low <= High loop
         pragma Loop_Invariant (Pos = 0);
         pragma Loop_Invariant (for all I in A'First .. Low - 1 => A (I) < Key);
         Mid := Low + (High - Low) / 2;
         if A (Mid) = Key then
            Pos := Mid;
            return;
         elsif A (Mid) < Key then
            Low := Mid + 1;
         else
            High := Mid - 1;
         end if;
      end loop;
   end Find;

end Search;
