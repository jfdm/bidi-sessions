module Sessions.Types.Local.Merge.Fold

import Decidable.Equality

import Data.SnocList
import Data.SnocList.Elem

import public Extra

import Sessions.Types.Local
import Sessions.Types.Local.Merge.Projection

%default total

public export
data Reduce : (xs : List (Local rs fs))
           -> (z   :       Local rs fs)
           -> Type
  where
    Last : Reduce [x] x
    Next : {z,q : _}
        -> Reduce xs z
        -> Projection.Merge x z q
        -> Reduce (x::xs) q

Uninhabited (Reduce [] z) where
  uninhabited Last impossible
  uninhabited (Next x y w) impossible

export
unique : Reduce xs a
      -> Reduce xs b
      -> a === b
unique Last Last = Refl
unique (Next xs xc) (Next ys zq) with (unique xs ys)
    unique (Next xs xq) (Next ys yq) | Refl with (unique xq yq)
      unique (Next xs xq) (Next ys yq) | Refl | Refl = Refl

finalMergeFails : (DPair (Local rs fs) (Merge x z) -> Void) -> Reduce (y :: xs) z
               -> DPair (Local rs fs) (Reduce  (x :: (y :: xs))) -> Void
finalMergeFails f w (fst ** (Next v s)) with (unique w v)
  finalMergeFails f w (fst ** (Next v s)) | Refl = f (fst ** s)

export
reduce : (xs : List (Local rs fs))
            -> Dec (DPair (Local rs fs) (Reduce xs))
reduce []
  = No $ \case (fst ** snd) => absurd snd

reduce (x :: [])
  = Yes (x ** Last)

reduce (x :: y :: xs) with (reduce (y::xs))
  reduce (x :: y :: xs) | (Yes (z ** pZ)) with (merge x z)
    reduce (x :: y :: xs) | (Yes (z ** pZ)) | (Yes (fst ** snd))
      = Yes (fst ** Next pZ snd)
    reduce (x :: y :: xs) | (Yes (z ** pZ)) | (No no)
      = No (finalMergeFails no pZ)
  reduce (x :: y :: xs) | (No contra)
    = No $ \case ((fst ** (Next z w))) => (contra (_ ** z))

-- [ EOF ]
