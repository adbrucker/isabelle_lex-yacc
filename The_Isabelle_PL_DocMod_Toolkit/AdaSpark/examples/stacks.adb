package body Stacks
  with SPARK_Mode
is

   procedure Push (S : in out Stack; X : Integer) is
   begin
      S.Top := S.Top + 1;
      S.Data (S.Top) := X;
   end Push;

   procedure Pop (S : in out Stack; X : out Integer) is
   begin
      X := S.Data (S.Top);
      S.Top := S.Top - 1;
   end Pop;

end Stacks;
