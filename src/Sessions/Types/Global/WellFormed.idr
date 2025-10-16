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
data SomeProject : (g  : Global rs Lin)
               -> (xs : Role.Context)
                     -> Type
  where
    Last : SomeProject g Lin

    Keep : {n : _}
        -> (idx : AtIndex r rs n)
        -> Project idx g l
        -> SomeProject g xs
        -> SomeProject g (xs :< r)


    Skip : {n : _}
        -> (idx : AtIndex r rs n)
        -> (DPair (Local rs Lin) (Project idx g) -> Void)
        -> SomeProject g xs
        -> SomeProject g (xs :< r)


someProject : {rs : Role.Context}
           -> (g : Global rs Lin)
           -> (xs : Role.Context)
                  -> Dec (SomeProject g xs)
someProject g [<]
  = Yes Last

someProject g (sx :< x) with (lookup rs x)
  someProject g (sx :< x) | (Yes (n ** idx)) with (project idx g)
    someProject g (sx :< x) | (Yes (n ** idx)) | (Yes (l ** prf)) with (someProject g sx)
      someProject g (sx :< x) | (Yes (n ** idx)) | (Yes (l ** p)) | (Yes ps)
        = Yes (Keep idx p ps)
      someProject g (sx :< x) | (Yes (n ** idx)) | (Yes (l ** p)) | (No no)
        = No (\case (Keep y z w) => no w
                    (Skip y f z) => no z)

    someProject g (sx :< x) | (Yes (n ** idx)) | (No noH) with (someProject g sx)
      someProject g (sx :< x) | (Yes (n ** idx)) | (No noH) | (Yes prf)
        = Yes $ Skip idx noH prf

      someProject g (sx :< x) | (Yes (n ** idx)) | (No noH) | (No no)
        = No $ \case (Keep y z w) => no w
                     (Skip y f z) => no z

  someProject g (sx :< x) | (No no)
    = No $ \case (Keep idx y z) => no (_ ** idx)
                 (Skip idx f y) => no (_ ** idx)

public export
data WellFormed : (rs : Role.Context)
               -> (g  : Global rs Lin)
                     -> Type
  where
    WF : SomeProject g rs -> WellFormed rs g

export
wellformed : {rs : Role.Context}
          -> (g  : Global rs Lin)
                -> Dec (WellFormed rs g)
wellformed {rs} g with (someProject g rs)
  wellformed {rs} g | (Yes prf)
    = Yes (WF prf)
  wellformed {rs} g | (No no)
    = No $ \case (WF x) => no x

-- [ EOF ]
