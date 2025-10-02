module Extra

import Decidable.Equality

import Data.SnocList
import Data.SnocList.Elem


noHR : (the (Elem x (xs :< x)) Here) = the (Elem y (ys :< y')) (There z) -> Void
noHR Refl impossible

noRH : the (Elem y (ys :< y')) (There z) = (the (Elem x (xs :< x)) Here) -> Void
noRH Refl impossible

public export
decEq : {0 xs : SnocList a}
     -> (ix : Elem x xs)
     -> (yx : Elem y xs)
     -> Dec (ix = yx)
decEq Here Here
  = Yes Refl
decEq Here (There z)
  = No noHR
decEq (There z) Here
  = No noRH
decEq (There z) (There y) with (decEq z y)
  decEq (There z) (There z) | (Yes Refl) = Yes Refl
  decEq (There z) (There y) | (No contra)
    = No (\case Refl => contra Refl)


namespace List

  public export
  data Shape : (xs,ys : List a) -> Type
    where
      End : Shape [] []
      LH : Shape (x::xs) Nil
      RH : Shape Nil (y::ys)
      B : Shape (x::xs) (y::ys)

  export
  shape : (xs, ys : List a ) -> Shape xs ys
  shape [] [] = End
  shape [] (x :: xs) = RH
  shape (x :: xs) [] = LH
  shape (x :: xs) (y :: ys) = B


  namespace Lookup

    Uninhabited (v : value ** Elem (k,v) Lin) where
      uninhabited (_ ** Here) impossible


    export
    lookup : DecEq key
          => (k : key)
          -> (store : SnocList (key,value))
                   -> Dec (v : value ** Elem (k,v) store)
    lookup k [<]
      = No absurd
    lookup k (sx :< (k',v)) with (decEq k k')
      lookup k (sx :< (k,v)) | (Yes Refl)
        = Yes (v ** Here)
      lookup k (sx :< (k',v)) | (No no) with (lookup k sx)
        lookup k (sx :< (k',v)) | (No no) | (Yes (v' ** idx))
          = Yes (v' ** There idx)
        lookup k (sx :< (k',v)) | (No no) | (No contra)
          = No (\case (v ** Here) => no Refl
                      (fst ** (There x)) => contra (fst ** x))

-- [ EOF ]
