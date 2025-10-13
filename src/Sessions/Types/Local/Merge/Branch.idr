module Sessions.Types.Local.Merge.Branch

import Decidable.Equality

import Data.SnocList
import Data.SnocList.Elem

import public Extra

import Sessions.Types.Local
import Sessions.Types.Local.Difference

%default total

public export
data Merge : (how : (a,b,c : Local rs fs) -> Type) -> (x,y,z : Branch rs fs) -> Type where
  B : (lx = ly)
   -> (tx = ty)
   -> how kx ky kz
   -> Merge how
            (B lx tx kx)
            (B ly ty ky)
            (B lx tx kz)

export
merge : (f   : (a,b : Local rs fs) -> Dec $ DPair (Local rs fs) (how a b))
     -> (x,y : Branch rs fs)
            -> Dec (DPair (Branch rs fs) (Merge how x y))

merge f (B lx tx kx) (B ly ty ky) with (Equality.decEq lx ly)
  merge f (B lx tx kx) (B lx ty ky) | (Yes Refl) with (decEq tx ty)
    merge f (B lx tx kx) (B lx tx ky) | (Yes Refl) | (Yes Refl) with (f kx ky)
      merge f (B lx tx kx) (B lx tx ky) | (Yes Refl) | (Yes Refl) | (Yes (ty ** prf))
        = Yes (B lx tx ty ** B Refl Refl prf)
      merge f (B lx tx kx) (B lx tx ky) | (Yes Refl) | (Yes Refl) | (No contra)
        = No (\case (B _ _ ty ** B _ _ prf) => contra (ty ** prf))


    merge f (B lx tx kx) (B lx ty ky) | (Yes Refl) | (No contra)
      = No (\case (B _ _ _ ** B _ Refl _) => contra Refl)

  merge f (B lx tx kx) (B ly ty ky) | (No contra)
    = No (\case (B _ _ _ ** B Refl _ _) => contra Refl)

export
unique : {0 how : (a,b,c : Local rs fs) -> Type}
      -> (f : {0 a,b,c,d : Local rs fs}
           -> (  this : how a b c)
           -> (  that : how a b d)
           -> c === d)
      -> (this : Merge how x y a)
      -> (that : Merge how x y b)
      -> a === b
unique f (B Refl Refl x) (B Refl Refl y) with (f x y)
  unique f (B Refl Refl x) (B Refl Refl y) | Refl = Refl

-- [ EOF ]
