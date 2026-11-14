--  Discriminated records, case expressions and contract cases.

package Shapes
  with SPARK_Mode
is
   type Kind is (Circle, Rectangle, Triangle);

   type Shape (K : Kind := Circle) is record
      Id : Positive := 1;
      case K is
         when Circle =>
            Radius : Positive := 1;
         when Rectangle =>
            Width, Height : Positive := 1;
         when Triangle =>
            Base, Altitude : Positive := 1;
      end case;
   end record;

   function Area (S : Shape) return Natural
     with Post => (case S.K is
                     when Circle    => Area'Result >= 3 * S.Radius ** 2,
                     when Rectangle => Area'Result = S.Width * S.Height,
                     when Triangle  => Area'Result = S.Base * S.Altitude / 2);

   function Clamp (X : Integer; Lo, Hi : Integer) return Integer
     with Pre            => Lo <= Hi,
          Contract_Cases => (X < Lo => Clamp'Result = Lo,
                             X > Hi => Clamp'Result = Hi,
                             others => Clamp'Result = X);

end Shapes;
