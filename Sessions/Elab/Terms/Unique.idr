module Sessions.Elab.Terms.Unique

import Sessions.Types.Local
import Sessions.Types.Local.Subset
import Sessions.Types.Local.Merge.Synthesis
import Sessions.AST

import Sessions.Elab.Expr
import Sessions.Elab.Local
import Sessions.Elab.Terms.Core

%default total

mutual
  namespace Synth
    namespace Branches
      export
      uniques : Branches.Synth rs fs ts xs tm as
             -> Branches.Synth rs fs ts xs tm bs
             -> as === bs
      uniques End End = Refl
      uniques (Ext x xs) (Ext y ys) with (unique x y)
        uniques (Ext x xs) (Ext y ys) | Refl with (uniques xs ys)
          uniques (Ext x xs) (Ext y ys) | Refl | Refl = Refl

    namespace Cases
      export
      uniques : Cases.Synth rs fs ts xs tm as
             -> Cases.Synth rs fs ts xs tm bs
             -> as === bs
      uniques End End = Refl
      uniques (Ext x xs) (Ext y ys) with (unique x y)
        uniques (Ext x xs) (Ext y ys) | Refl with (uniques xs ys)
          uniques (Ext x xs) (Ext y ys) | Refl | Refl = Refl


    export
    unique : Core.Synth rs fs ts tm a
          -> Core.Synth rs fs ts tm b
          -> a === b
    unique Stop Stop = Refl
    unique (Call n idx) (Call n idy) with (unique idx idy)
      unique (Call n idx) (Call n idy) | Refl with (unique2 idx idy)
        unique (Call n idy) (Call n idy) | Refl | Refl = Refl

    unique (Loop x) (Loop y) with (unique x y)
      unique (Loop x) (Loop y) | Refl = Refl

    unique (Send rx vx x) (Send ry vy y) with (unique rx ry)
      unique (Send rx vx x) (Send ry vy y) | Refl with (unique vx vy)
        unique (Send rx vx x) (Send ry vy y) | Refl | Refl with (unique2 rx ry)
          unique (Send rx vx x) (Send rx vy y) | Refl | Refl | Refl with (unique x y)
            unique (Send rx vx x) (Send rx vy y) | Refl | Refl | Refl | Refl = Refl

    unique (Recv rx xs) (Recv ry ys) with (unique rx ry)
      unique (Recv rx xs) (Recv ry ys) | Refl with (unique2 rx ry)
        unique (Recv ry xs) (Recv ry ys) | Refl | Refl with (uniques xs ys)
          unique (Recv ry xs) (Recv ry ys) | Refl | Refl | Refl = Refl


    unique (The x px) (The y py) with (Local.unique x y)
      unique (The x px) (The y py) | Refl = Refl

    unique (If cx tx fx px) (If cy ty fy py) with (unique tx ty)
      unique (If cx tx fx px) (If cy ty fy py) | Refl with (unique fx fy)
        unique (If cx tx fx px) (If cy ty fy py) | Refl | Refl with (unique px py)
          unique (If cx tx fx px) (If cy ty fy py) | Refl | Refl | Refl = Refl

    unique (Match mx cx px) (Match my cy py) with (unique mx my)
      unique (Match mx cx px) (Match my cy py) | Refl with (uniques cx cy)
        unique (Match mx cx px) (Match my cy py) | Refl | Refl with (unique px py)
          unique (Match mx cx px) (Match my cy py) | Refl | Refl | Refl = Refl
-- [ EOF ]
