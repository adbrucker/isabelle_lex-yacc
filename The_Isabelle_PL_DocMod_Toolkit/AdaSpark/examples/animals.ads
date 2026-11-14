--  A tagged type with a private extension.

package Animals
  with SPARK_Mode
is
   type Animal is tagged private;

   function Legs (A : Animal) return Natural;

   procedure Grow_Leg (A : in out Animal)
     with Post => Legs (A) = Legs (A'Old) + 1;

private

   type Animal is tagged record
      N : Natural := 4;
   end record;

end Animals;
