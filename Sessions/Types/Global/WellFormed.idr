module Sessions.Types.Global.WellFormed

import Decidable.Equality

import Data.SnocList
import Data.SnocList.Elem

import  Extra

import Sessions.Types.Global
import Sessions.Types.Local
import Sessions.Types.Global.Projection

%default total


public export
data All : (g  : Global rs Lin)
               -> (xs : Role.Context)
                     -> Type
  where
    Last : All g Lin

    Keep : {n : _}
        -> (idx : AtIndex r rs n)
        -> Project idx g l
        -> All g xs
        -> All g (xs :< r)


    Skip : {n : _}
        -> (idx : AtIndex r rs n)
        -> (DPair (Local rs Lin) (Project idx g) -> Void)
        -> All g xs
        -> All g (xs :< r)


all : {rs : Role.Context}
  -> (g : Global rs Lin)
  -> (xs : Role.Context)
       -> Dec (All g xs)
all g [<]
  = Yes Last

all g (sx :< x) with (lookup rs x)
  all g (sx :< x) | (Yes (n ** idx)) with (project idx g)
    all g (sx :< x) | (Yes (n ** idx)) | (Yes (l ** prf)) with (all g sx)
      all g (sx :< x) | (Yes (n ** idx)) | (Yes (l ** p)) | (Yes ps)
        = Yes (Keep idx p ps)
      all g (sx :< x) | (Yes (n ** idx)) | (Yes (l ** p)) | (No no)
        = No (\case (Keep y z w) => no w
                    (Skip y f z) => no z)

    all g (sx :< x) | (Yes (n ** idx)) | (No noH) with (all g sx)
      all g (sx :< x) | (Yes (n ** idx)) | (No noH) | (Yes prf)
        = Yes $ Skip idx noH prf

      all g (sx :< x) | (Yes (n ** idx)) | (No noH) | (No no)
        = No $ \case (Keep y z w) => no w
                     (Skip y f z) => no z

  all g (sx :< x) | (No no)
    = No $ \case (Keep idx y z) => no (_ ** idx)
                 (Skip idx f y) => no (_ ** idx)

public export
data WellFormed : (rs : Role.Context)
               -> (g  : Global rs Lin)
                     -> Type
  where
    WF : All g rs -> WellFormed rs g

export
wellformed : {rs : Role.Context}
          -> (g  : Global rs Lin)
                -> Dec (WellFormed rs g)
wellformed {rs} g with (all g rs)
  wellformed {rs} g | (Yes prf)
    = Yes (WF prf)
  wellformed {rs} g | (No no)
    = No $ \case (WF x) => no x

-- [ EOF ]
