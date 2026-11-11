--  A bounded stack of integers with SPARK contracts.

package Stacks
  with SPARK_Mode
is
   Capacity : constant := 100;

   subtype Count_Type is Natural range 0 .. Capacity;
   subtype Index_Type is Positive range 1 .. Capacity;

   type Element_Array is array (Index_Type) of Integer;

   type Stack is record
      Top  : Count_Type := 0;
      Data : Element_Array := (others => 0);
   end record;

   function Is_Empty (S : Stack) return Boolean is (S.Top = 0);

   function Is_Full (S : Stack) return Boolean is (S.Top = Capacity);

   procedure Push (S : in out Stack; X : Integer)
     with Pre  => not Is_Full (S),
          Post => S.Top = S.Top'Old + 1 and then S.Data (S.Top) = X;

   procedure Pop (S : in out Stack; X : out Integer)
     with Pre  => not Is_Empty (S),
          Post => S.Top = S.Top'Old - 1 and X = S.Data (S.Top'Old);

end Stacks;
