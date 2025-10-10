module Sessions.Elab.Global

import Extra

import Sessions.Types.Common
import Sessions.Types.Global
import Sessions.AST

%default total

namespace Synth
  namespace Local
    namespace Branches
      public export
      data Global : (how : (rs : SnocList Role)
                       -> (fs : Fix.Context)
                       -> (tm : Global)
                       -> (ty : Global rs fs)
                             -> Type)
                -> (rs  : SnocList Role)
                -> (fs  : Fix.Context)
                -> (tms : List (String, Base, Global))
                -> (tys : List (Branch rs fs))
                       -> Type
        where
          End : Global how rs fs Nil Nil
          Ext : {0 how : (rs : SnocList Role)
                      -> (fs : Fix.Context)
                      -> (tm : Global)
                      -> (ty : Global rs fs)
                            -> Type}
             -> (head : how rs fs ktm kty)
             -> (next : Global how rs fs tms tys)
                     -> Global how rs fs ((l,b,ktm)::tms) (B l b kty :: tys)

namespace Synth
  namespace Global

    public export
    data Global : (rs : SnocList Role)
              -> (fs : Fix.Context)
              -> (tm : Global)
              -> (ty : Global rs fs)
                    -> Type
      where
        End : Global rs fs End Stop
        Call : (n : Nat)
            -> (idx : AtIndex MkFix fs n)
                   -> Global rs fs (Call n) (Call idx)

        Rec : Global rs (fs :< MkFix) kast kty
           -> Global rs fs (Rec kast) (Rec kty)

        Choice : (s : Nat)
              -> (ids : AtIndex n rs s)
              -> (r : Nat)
              -> (idr : AtIndex m rs r)
              -> (prf : EqualNot ids idr)
              -> Global Global rs fs tms tys
              -> Global rs fs (Choice s r tms) (Choice ids idr prf tys)

mutual
  namespace Synth
    namespace Global
      namespace Branches
        export
        synth : {0 how : (rs : SnocList Role)
                      -> (fs : Fix.Context)
                      -> (tm : Global)
                      -> (ty : Global rs fs)
                            -> Type}
             -> (f : (rs : SnocList Role)
                  -> (fs : Fix.Context)
                  -> (tm : Global)
                        -> Dec (DPair (Global rs fs) (how rs fs tm)))
             -> (rs  : SnocList Role)
             -> (fs  : Fix.Context)
             -> (tms : List (String, Base, Global))
                    -> Dec (DPair (List (Branch rs fs))
                                  (Branches.Global how rs fs tms))
        synth f rs fs []
          = Yes ([] ** End)
        synth f rs fs ((l,t,x) :: xs) with (f rs fs x)
          synth f rs fs ((l,t,x) :: xs) | (Yes (g ** pG)) with (synth f rs fs xs)
            synth f rs fs ((l,t,x) :: xs) | (Yes (g ** pG)) | (Yes (gs ** pGS))
              = Yes (B l t g :: gs ** Ext pG pGS)
            synth f rs fs ((l,t,x) :: xs) | (Yes (g ** pG)) | (No no)
              = No $ \case ((B l t kty :: tys) ** (Ext head next)) => no (tys ** next)
          synth f rs fs ((l,t,x) :: xs) | (No no)
            = No $ \case ((B l t kty :: tys) ** (Ext head next)) => no (kty ** head)


  namespace Synth

    namespace Global


      failsSameSR : a === b -> DPair (Global rs fs) (Global rs fs (Choice a b bs)) -> Void
      failsSameSR Refl (Choice ids idr notSame _ ** Choice s ids s idr notSame _) with (unique ids idr)
        failsSameSR Refl (Choice ids idr notSame _ ** Choice s ids s idr notSame _) | Refl with (unique2 ids idr)
          failsSameSR Refl (Choice ids ids notSame _ ** Choice s ids s ids notSame _) | Refl | Refl
            = toVoid Refl notSame

      export
      synth : (rs : SnocList Role)
           -> (fs : Fix.Context)
           -> (tm : Global)
                 -> Dec (DPair (Global rs fs)
                               (Global rs fs tm))
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

      synth rs fs (Choice s r bs) with (index rs s)
        synth rs fs (Choice s r bs) | (Yes (s' ** ids)) with (index rs r)
          synth rs fs (Choice s r bs) | (Yes (s' ** ids)) | (Yes (r' ** idr)) with (decEqAlt' ids idr)
            synth rs fs (Choice s r bs) | (Yes (s' ** ids)) | (Yes (r' ** idr)) | (Left notSame) with (synth synth rs fs bs)
              synth rs fs (Choice s r bs) | (Yes (s' ** ids)) | (Yes (r' ** idr)) | (Left notSame) | (Yes (gbs ** prf))
                = Yes (Choice ids idr ?sa gbs ** Choice s ids r idr notSame prf)
              synth rs fs (Choice s r bs) | (Yes (s' ** ids)) | (Yes (r' ** idr)) | (Left notSame) | (No no)
                = No $ \case (((Choice x y prf tys) ** (Choice s x r y prf z))) => no (tys ** z)
            synth rs fs (Choice r r bs) | (Yes (r' ** idr)) | (Yes (r' ** idr)) | (Right Refl)
              = No (failsSameSR Refl)

          synth rs fs (Choice s r bs) | (Yes (s' ** ids)) | (No no)
            = No $ \case (((Choice x idr prf tys) ** (Choice s x r idr prf y))) => no (_ ** idr)

        synth rs fs (Choice s r bs) | (No no)
          = No $ \case (((Choice ids idr prf tys) ** (Choice s ids r idr prf x))) => no (_ ** ids)

mutual
    namespace Global
      uniques : Global Global rs fs tms as
             -> Global Global rs fs tms bs
             -> as === bs
      uniques End End = Refl
      uniques (Ext x xs) (Ext y ys) with (unique x y)
        uniques (Ext x xs) (Ext y ys) | Refl with (uniques xs ys)
          uniques (Ext x xs) (Ext y ys) | Refl | Refl = Refl

      export
      unique : Global rs fs tm a
            -> Global rs fs tm b
            -> a === b
      unique End End = Refl
      unique (Call n x) (Call n y) with (unique x y)
        unique (Call n x) (Call n y) | Refl with (unique2 x y)
          unique (Call n x) (Call n x) | Refl | Refl = Refl

      unique (Rec x) (Rec y) with (unique x y)
        unique (Rec x) (Rec y) | Refl = Refl
      unique (Choice s xids r xidr xprf xxs) (Choice s yids r yidr yprf yys) with (unique xids yids)
        unique (Choice s xids r xidr xprf xxs) (Choice s yids r yidr yprf yys) | Refl with (unique2 xids yids)
          unique (Choice s yids r xidr xprf xxs) (Choice s yids r yidr yprf yys) | Refl | Refl with (unique xidr yidr)
            unique (Choice s yids r xidr xprf xxs) (Choice s yids r yidr yprf yys) | Refl | Refl | Refl with (unique2 xidr yidr)
              unique (Choice s yids r yidr xprf xxs) (Choice s yids r yidr yprf yys) | Refl | Refl | Refl | Refl with (unique xprf yprf)
                unique (Choice s yids r yidr xprf xxs) (Choice s yids r yidr xprf yys) | Refl | Refl | Refl | Refl | Refl with (uniques xxs yys)
                  unique (Choice s yids r yidr xprf xxs) (Choice s yids r yidr xprf yys) | Refl | Refl | Refl | Refl | Refl | Refl = Refl

-- [ EOF ]
