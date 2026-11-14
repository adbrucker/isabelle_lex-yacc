with Ada.Text_IO; use Ada.Text_IO;

procedure Hello is
   Greeting : constant String := "Hello, " & "SPARK!";
   Count    : Integer := 0;
begin
   for I in reverse 1 .. 3 loop
      Put_Line (Greeting);
      Count := Count + I;
   end loop;
   if Count > 5 then
      Put_Line ("many");
   end if;
exception
   when Constraint_Error =>
      Put_Line ("error");
end Hello;
