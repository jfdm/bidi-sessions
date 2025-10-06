module Sessions.Types.Local.Subset

import Decidable.Equality

import Data.SnocList
import Data.SnocList.Elem

import public Extra

import Sessions.Types.Local


namespace Branch
  public export
  data Subset : (how : (a,b : Local rs fs) -> Type) -> (x,y : Branch rs fs) -> Type where
    B : (lx = ly)
     -> (tx = ty)
     -> how kx ky
     -> Subset how
              (B lx tx kx)
              (B ly ty ky)

  export
  subset : (f   : (a,b : Local rs fs) -> Dec (how a b))
        -> (x,y : Branch rs fs)
               -> Dec (Subset how x y)
  subset f (B lx tx kx) (B ly ty ky) with (Equality.decEq lx ly)
    subset f (B lx tx kx) (B lx ty ky) | (Yes Refl) with (decEq tx ty)
      subset f (B lx tx kx) (B lx tx ky) | (Yes Refl) | (Yes Refl) with (f kx ky)
        subset f (B lx tx kx) (B lx tx ky) | (Yes Refl) | (Yes Refl) | (Yes prf)
          = Yes (B Refl Refl prf)
        subset f (B lx tx kx) (B lx tx ky) | (Yes Refl) | (Yes Refl) | (No contra)
          = No (\case (B _ _ x) => contra x)

      subset f (B lx tx kx) (B lx ty ky) | (Yes Refl) | (No contra)
        = No (\case (B _ prf _) => contra prf)

    subset f (B lx tx kx) (B ly ty ky) | (No contra)
      = No (\case (B prf _ _ ) => contra prf)

namespace Branches


  public export
  data Subset : (how : (a,b : Local rs fs) -> Type)
             -> (xs : List (Branch rs fs))
             -> (ys : List (Branch rs fs))
                   -> Type where
    ||| Ran out of left branches
    Stop : Subset how Nil ys

    ||| If branches match then go to next x and y
    Keep : Subset how  x       y
        -> Subset how     xs      ys
        -> Subset how (x::xs) (y::ys)

    ||| If branches do not match shift down the ys.
    Skip : Not (Subset how  x       y)
        ->      Subset how (x::xs)     ys
        ->      Subset how (x::xs) (y::ys)


  isEmpty : Subset how (x :: xs) [] -> Void
  isEmpty Stop impossible
  isEmpty (Keep y z) impossible
  isEmpty (Skip f y) impossible

  export
  subset : (f     : (a,b : Local rs fs) -> Dec (how a b))
        -> (xs,ys : List $ Branch rs fs)
                 -> Dec (Subset how xs ys)
  subset f [] ys
    = Yes Stop

  subset f (x :: xs) []
    = No isEmpty

  subset f (x :: xs) (y :: ys) with (subset f x y)
    subset f (x :: xs) (y :: ys) | (Yes pH) with (subset f xs ys)
      subset f (x :: xs) (y :: ys) | (Yes pH) | (Yes pT)
        = Yes (Keep pH pT)
      subset f (x :: xs) (y :: ys) | (Yes pH) | (No contra)
        = No (\case (Keep z w) => contra w
                    (Skip g z) => g pH)

    subset f (x :: xs) (y :: ys) | (No contra) with (subset f (x::xs) ys)
      subset f (x :: xs) (y :: ys) | (No noH) | (Yes prf)
        = Yes (Skip noH prf)

      subset f (x :: xs) (y :: ys) | (No noH) | (No noL)
        = No (\case (Keep pH _) => noH pH
                    (Skip nH pL) => noL pL)

public export
data Subset : (x,y : Local rs fs)
           -> Type

  where
    Stop : Subset Stop Stop
    Call : Equal idxx idxy
        -> Subset (Call idxx)
                  (Call idxy)
    Rec : Subset kx ky
       -> Subset (Rec kx)
                 (Rec ky)

    Comm : (cx = cy)
        -> (sx = sy)
        -> Branches.Subset Subset kx ky
        -> Subset (Comm cx sx kx)
                  (Comm cy sy ky)


subsetSC : (Subset Stop (Call x)) -> Void
subsetSC _ impossible

subsetSR : (Subset Stop (Rec s)) -> Void
subsetSR _ impossible

subsetSM : (Subset Stop (Comm x y xs)) -> Void
subsetSM _ impossible

subsetCR : (Subset (Call idx) (Rec s)) -> Void
subsetCR _ impossible

subsetCM : (Subset (Call idx) (Comm z x s)) -> Void
subsetCM _ impossible

subsetCS : (Subset (Call x) Stop ) -> Void
subsetCS _ impossible

subsetRS : (Subset (Rec s) Stop) -> Void
subsetRS _ impossible

subsetRC: (Subset (Rec  s) (Call idx) ) -> Void
subsetRC _ impossible

subsetRM: (Subset (Rec  s) (Comm a w idx) ) -> Void
subsetRM _ impossible


subsetMS : (Subset (Comm x y xs) Stop) -> Void
subsetMS _ impossible

subsetMC : (Subset  (Comm z x s) (Call idx)) -> Void
subsetMC _ impossible

subsetMR: (Subset (Comm a w idx) (Rec s)) -> Void
subsetMR _ impossible

export
subset : (x,y : Local rs fs)
             -> Dec (Subset x y)
subset Stop Stop
  = Yes Stop
subset Stop (Call _)
  = No subsetSC
subset Stop (Rec  _)
  = No subsetSR
subset Stop (Comm _ _ _)
  = No subsetSM

subset (Call _) Stop
  = No subsetCS

subset (Call x) (Call y) with (decEq x y)
  subset (Call x) (Call y) | (Yes prf)
    = Yes (Call prf)
  subset (Call x) (Call y) | (No no)
    = No (\case (Call prf) => no prf)

subset (Call _) (Rec  _)
  = No subsetCR
subset (Call _) (Comm _ _ _)
  = No subsetCM

subset (Rec _) Stop
  = No subsetRS
subset (Rec _) (Call _)
  = No subsetRC
subset (Rec kx) (Rec ky) with (subset kx ky)
  subset (Rec kx) (Rec ky) | (Yes prf)
    = Yes (Rec prf)
  subset (Rec kx) (Rec ky) | (No no)
    = No (\case (Rec x) => no x)

subset (Rec _) (Comm _ _ _)
  = No subsetRM

subset (Comm _ _ _) Stop
  = No subsetMS
subset (Comm _ _ _) (Call x)
  = No subsetMC
subset (Comm _ _ _) (Rec x)
  = No subsetMR
subset (Comm lx tx kx) (Comm ly ty ky) with (decEq lx ly)
  subset (Comm lx tx kx) (Comm lx ty ky) | (Yes Refl) with (decEq tx ty)
    subset (Comm lx tx kx) (Comm lx tx ky) | (Yes Refl) | (Yes Refl) with (subset subset kx ky)
      subset (Comm lx tx kx) (Comm lx tx ky) | (Yes Refl) | (Yes Refl) | (Yes prf)
        = Yes (Comm Refl Refl prf)
      subset (Comm lx tx kx) (Comm lx tx ky) | (Yes Refl) | (Yes Refl) | (No no)
        = No (\case (Comm _ _ prf) => no prf)

    subset (Comm lx tx kx) (Comm lx ty ky) | (Yes Refl) | (No no)
      = No (\case (Comm _ prf _) => no prf)

  subset (Comm lx tx kx) (Comm ly ty ky) | (No no)
    = No (\case (Comm prf _ _) => no prf)
-- [ EOF ]
