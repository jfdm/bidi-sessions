module Sessions.Elab.Local

import Extra

import Sessions.Types.Common
import Sessions.Types.Local
import Sessions.Types.Local.Subset
import Sessions.Types.Local.Merge.Synthesis
import Sessions.AST

%default total

mutual
  namespace Synth
    namespace Local
      namespace Branches
        public export
        data Local : (how : (rs : SnocList Role)
                         -> (fs : Fix.Context)
                         -> (tm : Local)
                         -> (ty : Local rs fs)
                               -> Type)
                  -> (rs  : SnocList Role)
                  -> (fs  : Fix.Context)
                  -> (tms : List (String, Base, Local))
                  -> (tys : List (Branch rs fs))
                         -> Type
          where
            End : Local how rs fs Nil Nil
            Ext : {0 how : (rs : SnocList Role)
                        -> (fs : Fix.Context)
                        -> (tm : Local)
                        -> (ty : Local rs fs)
                              -> Type}
               -> (head : how rs fs ktm kty)
               -> (next : Local how rs fs tms tys)
                       -> Local how rs fs ((l,b,ktm)::tms) (B l b kty :: tys)

        export
        synth : {0 how : (rs : SnocList Role)
                      -> (fs : Fix.Context)
                      -> (tm : Local)
                      -> (ty : Local rs fs)
                            -> Type}
             -> (f : (rs : SnocList Role)
                  -> (fs : Fix.Context)
                  -> (tm : Local)
                        -> Dec (DPair (Local rs fs) (how rs fs tm)))
             -> (rs  : SnocList Role)
             -> (fs  : Fix.Context)
             -> (tms : List (String, Base, Local))
                    -> Dec (DPair (List (Branch rs fs))
                                  (Branches.Local how rs fs tms))
        synth f rs fs []
          = Yes ([] ** End)

        synth f rs fs ((l,b,x) :: xs) with (f rs fs x)
          synth f rs fs ((l,b,x) :: xs) | (Yes (ty ** tm)) with (synth f rs fs xs)
            synth f rs fs ((l,b,x) :: xs) | (Yes (ty ** tm)) | (Yes (tys ** tms))
              = Yes (B l b ty :: tys ** Ext tm tms)
            synth f rs fs ((l,b,x) :: xs) | (Yes (ty ** tm)) | (No no)
              = No (\case ((B l b kty :: tys) ** (Ext head next)) => no (tys ** next))

          synth f rs fs ((l,b,x) :: xs) | (No noH)
            = No (\case ((B l b kty :: tys) ** (Ext head next)) => noH (kty ** head))

  namespace Synth
    namespace Local

      public export
      data Local : (rs : SnocList Role)
                -> (fs : Fix.Context)
                -> (tm : Local)
                -> (ty : Local rs fs)
                      -> Type
        where
          End : Local rs fs End Stop
          Call : (n : Nat)
              -> (idx : AtIndex MkFix fs n)
                     -> Local rs fs (Call n) (Call idx)

          Rec : Local rs (fs :< MkFix) kast kty
             -> Local rs fs (Rec kast) (Rec kty)

          Comm : {r : _}
              -> (n : Nat)
              -> (idx : AtIndex r rs n)
              -> Local Local rs fs tms tys
              -> Local rs fs (Comm cty n tms) (Comm cty idx tys)

      export
      synth : (rs : SnocList Role)
           -> (fs : Fix.Context)
           -> (tm : Local)
                 -> Dec (DPair (Local rs fs)
                               (Local rs fs tm))
      synth rs fs End
        = Yes (Stop ** End)

      synth rs fs (Call str) with (index fs str)
        synth rs fs (Call str) | (Yes (MkFix ** prf))
          = Yes (Call prf ** Call str prf)
        synth rs fs (Call str) | (No no)
          = No (\case ((Call idx) ** (Call str idx)) => no (_ ** idx) )

      synth rs fs (Rec k) with (synth rs (fs :< ( MkFix)) k)
        synth rs fs (Rec k) | (Yes (kty ** prf))
          = Yes (Rec kty ** Rec prf)
        synth rs fs (Rec k) | (No no)
          = No (\case ((Rec kty) ** (Rec x)) => no (kty ** x))

      synth rs fs (Comm cty n bs) with (index rs n)
        synth rs fs (Comm cty n bs) | (Yes ridx) with (synth synth rs fs bs)
          synth rs fs (Comm cty n bs) | (Yes (r ** ridx)) | (Yes (tys ** tms))
            = Yes (Comm cty ridx tys ** Comm n ridx tms)
          synth rs fs (Comm cty n bs) | (Yes ridx) | (No no)
            = No (\case ((Comm cty idx tys) ** (Comm n idx x)) => no (tys ** x))

        synth rs fs (Comm cty r bs) | (No no)
          = No (\case (Comm cty idx tys ** Comm n idx x) => no (_ ** idx))

    namespace Local
      mutual
        uniques : Local Local rs fs tms a
               -> Local Local rs fs tms b
               -> a === b
        uniques End End = Refl
        uniques (Ext x xs) (Ext y ys) with (unique x y)
          uniques (Ext x xs) (Ext y ys) | Refl with (uniques xs ys)
            uniques (Ext x xs) (Ext y ys) | Refl | Refl = Refl

        export
        unique : Local rs fs tm a
              -> Local rs fs tm b
              -> a === b
        unique End End = Refl
        unique (Call n idx) (Call n x) with (unique idx x)
          unique (Call n idx) (Call n x) | Refl with (unique2 idx x)
            unique (Call n x) (Call n x) | Refl | Refl = Refl

        unique (Rec x) (Rec y) with (unique x y)
          unique (Rec x) (Rec y) | Refl = Refl

        unique (Comm n idx xs) (Comm n idy ys) with (unique idx idy)
          unique (Comm n idx xs) (Comm n idy ys) | Refl with (unique2 idx idy)
            unique (Comm n idy xs) (Comm n idy ys) | Refl | Refl with (uniques xs ys)
              unique (Comm n idy xs) (Comm n idy ys) | Refl | Refl | Refl = Refl


-- [ EOF ]
