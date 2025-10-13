module Sessions.Types.Base

import Decidable.Equality

import Extra

%default total

public export
data Base = NAT | BOOL | SUM (List $ Pair String Base)

noSR : NAT = BOOL -> Void
noSR Refl impossible

noBV : BOOL = (SUM _) -> Void
noBV Refl impossible

noSV : NAT = (SUM _) -> Void
noSV Refl impossible



decEq : (a, b : Base) -> Dec (a === b)

decEqs : (as, bs : List (String, Base)) -> Dec (as === bs)

decEq NAT NAT = Yes Refl
decEq NAT BOOL
  = No noSR
decEq NAT (SUM xs)
  = No noSV

decEq BOOL NAT
  = No (negEqSym noSR)
decEq BOOL BOOL
  = Yes Refl
decEq BOOL (SUM xs)
  = No noBV

decEq (SUM xs) NAT
  = No (negEqSym noSV)

decEq (SUM xs) BOOL
  = No (negEqSym noBV)

decEq (SUM xs) (SUM ys) with (decEqs xs ys)
  decEq (SUM xs) (SUM xs) | (Yes Refl) = Yes Refl
  decEq (SUM xs) (SUM ys) | (No contra)
    = No $ \case Refl => contra Refl

decEqs [] [] = Yes Refl
decEqs [] (x :: xs)
  = No rightHeavy
decEqs (x :: xs) []
  = No leftHeavy
decEqs ((lx,x) :: xs) ((ly,y) :: ys) with (Equality.decEq lx ly)
  decEqs ((lx,x) :: xs) ((ly,y) :: ys) | (No contra)
    = No $ \case Refl => contra Refl

  decEqs ((lx,x) :: xs) ((lx,y) :: ys) | (Yes Refl) with (decEq x y)
    decEqs ((lx,x) :: xs) ((lx,y) :: ys) | (Yes Refl) | (No contra)
      = No $ \case Refl => contra Refl

    decEqs ((lx,x) :: xs) ((lx,x) :: ys) | (Yes Refl) | (Yes Refl) with (decEqs xs ys)
      decEqs ((lx,x) :: xs) ((lx,x) :: xs) | (Yes Refl) | (Yes Refl) | (Yes Refl) = Yes Refl
      decEqs ((lx,x) :: xs) ((lx,x) :: ys) | (Yes Refl) | (Yes Refl) | (No contra)
        = No $ \case Refl => contra Refl


export
DecEq Base where
  decEq = Base.decEq


public export
data IsSum : Base -> Type where
  YIS : IsSum (SUM xs)


natNoSum : IsSum NAT -> Void
natNoSum YIS impossible

boolNotSum : IsSum BOOL -> Void
boolNotSum YIS impossible

export
isSum : (b : Base) -> Dec (IsSum b)
isSum NAT
  = No natNoSum
isSum BOOL
  = No boolNotSum

isSum (SUM xs)
  = Yes YIS

-- [ EOF ]
