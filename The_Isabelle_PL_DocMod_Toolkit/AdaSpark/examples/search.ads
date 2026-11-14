--  Binary search in a sorted array, specified with quantified expressions.

package Search
  with SPARK_Mode
is
   type Int_Array is array (Positive range <>) of Integer;

   function Sorted (A : Int_Array) return Boolean is
     (for all I in A'First .. A'Last - 1 => A (I) <= A (I + 1));

   procedure Find (A : Int_Array; Key : Integer; Pos : out Natural)
     with Pre  => Sorted (A),
          Post => (if Pos /= 0 then Pos in A'Range and then A (Pos) = Key
                   else (for all I in A'Range => A (I) /= Key));
end Search;
