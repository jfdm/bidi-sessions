module Sessions.Elab

import Sessions.Types.Local
import Sessions.Types.Local.Subset
import Sessions.Types.Local.Merge.Synthesis
import Sessions.AST

import Sessions.Elab.Expr
import Sessions.Elab.Local

mutual
  namespace Branches
    public export
    data Synth : (rs : SnocList Role)
              -> (fs : SnocList Fix)
              -> (ts : SnocList (String,Base))
              -> (tms : List (String, String, Base, Synth.AST))
              -> (tys : List (Branch rs fs))
                     -> Type
      where
        End : Synth rs fs ts Nil Nil
        Ext : Synth rs fs (ts :< (v, b)) tm ty
           -> Synth rs fs ts tms tys
           -> Synth rs fs ts ((l,v,b,tm)::tms) (B l b ty :: tys)

  public export
  data Synth : (rs : SnocList Role)
            -> (fs : SnocList Fix)
            -> (ts : SnocList (String,Base))
            -> (tm : Synth.AST)
            -> (ty : Local rs fs)
                  -> Type
    where
      Stop : Synth rs fs ts Stop Stop
      Call : (n : Nat)
          -> (idx : AtIndex MkFix fs n)
                 -> Synth rs fs ts (Call n) (Call idx)

      Loop : (cont : Synth rs (fs :< (MkFix)) ts tm  ty)
                  -> Synth rs  fs    ts (Loop tm) (Rec ty)

      Send : {r : _}
          -> (prf  : AtIndex r rs n)
          -> (cont : Synth rs fs ts tm ty)
                  -> Synth rs fs ts (Send n l b tm)
                                 (Comm SEND prf [B l b ty])

      Recv : {r : _}
          -> (idx : AtIndex r rs n)
          -> (bs  : Synth rs fs ts tms tys)
                 -> Synth rs fs ts (Recv n tms) (Comm RECV idx tys)

      If : (l,r : Local rs fs)
        -> (cond : Expr ts BOOL c)
        -> (tt   : Synth rs fs ts ttm l)
        -> (ff   : Synth rs fs ts ffm r)
        -> (prf  : Merge l r ty)
                -> Synth rs fs ts (If c ttm ffm) ty

      The : Local rs fs    tmty ty
         -> Check rs fs ts ty tm
         -> Synth rs fs ts (The tmty tm) ty

  public export
  data Check : (rs : SnocList Role)
            -> (fs : SnocList (Fix))
            -> (ts : SnocList (String,Base))
           -> (ty : Local rs fs)
            -> (tm : Check.AST)
                  -> Type
    where
      Switch : (tySyn : Local rs fs)
            -> Synth rs fs ts tm tySyn
            -> Subset tySyn tyCheck
            -> Check rs fs ts tyCheck (Switch tm)

namespace Check
  export
  unique : Check rs fs ts a tm
        -> Check rs fs ts b tm
        -> a === b

namespace Branches
  export
  synth : (rs : SnocList Role)
       -> (fs : SnocList (Fix))
       -> (ts : SnocList (String,Base))
       -> (tms : List (String, String, Base, Synth.AST))
              -> Dec (DPair (List (Branch rs fs))
                            (Synth rs fs ts tms))

export
synth : (rs : SnocList Role)
     -> (fs : SnocList (Fix))
     -> (ts : SnocList (String,Base))
     -> (tm : Synth.AST)
           -> Dec (DPair (Local rs fs)
                         (Synth rs fs ts tm))

export
check : (rs : SnocList Role)
     -> (fs : SnocList (Fix))
     -> (ts : SnocList (String,Base))
     -> (ty : Local rs fs)
     -> (tm : Check.AST)
           -> Dec (Check rs fs ts ty tm)


namespace Branches
  synth rs fs ts []
    = Yes ([] ** End)
  synth rs fs ts ((l,v,b,k) :: xs) with (synth rs fs (ts :< (v,b)) k)
    synth rs fs ts ((l,v,b,k) :: xs) | (Yes (ty ** tm)) with (synth rs fs ts xs)
      synth rs fs ts ((l,v,b,k) :: xs) | (Yes (ty ** tm)) | (Yes (tys ** tms))
        = Yes (B l b ty :: tys ** Ext tm tms)
      synth rs fs ts ((l,v,b,k) :: xs) | (Yes (ty ** tm)) | (No no)
        = No (\case ((B l b ty :: tys) ** (Ext x y)) => no (tys ** y))

    synth rs fs ts ((l,v,b,k) :: xs) | (No no)
      = No (\case ((B l b ty :: tys) ** (Ext x y)) => no (ty ** x))


mergeFails : Synth rs fs ts tt tyL
          -> Synth rs fs ts ff tyR
          -> (DPair (Local rs fs) (Merge tyL tyR) -> Void)
          -> DPair (Local rs fs) (Synth rs fs ts (If c tt ff)) -> Void
mergeFails px py f (fst ** (If l r cond pl pr prf)) = ?mergeFails_rhs_1

checkFails : Local rs fs typetm type
          -> (Check rs fs ts type tm -> Void)
          -> DPair (Local rs fs)
                   (Synth rs fs ts (The typetm tm))
          -> Void
checkFails pl f (ty ** (The x y)) with (unique pl x)
  checkFails pl f (ty ** (The x y)) | Refl = f y

synth rs fs ts Stop
  = Yes (Stop ** Stop)

synth rs fs ts (Call str) with (index fs str)
  synth rs fs ts (Call str) | (Yes (MkFix ** prf))
    = Yes (Call prf ** Call str prf)
  synth rs fs ts (Call str) | (No no)
    = No (\case ((Call idx) ** (Call n idx)) => no (_ ** idx))

synth rs fs ts (Loop k) with (synth rs (fs :< (MkFix)) ts k)
  synth rs fs ts (Loop k) | (Yes (ty ** prf))
    = Yes (Rec ty ** Loop prf)
  synth rs fs ts (Loop k) | (No no)
    = No (\case ((Rec ty) ** (Loop cont)) => no (ty ** cont))

synth rs fs ts (Send r l ty k) with (index rs r)
  synth rs fs ts (Send r l ty k) | (Yes ridx) with (synth rs fs ts k)
    synth rs fs ts (Send r l ty k) | (Yes (n ** ridx)) | (Yes (lty ** prf))
      = Yes (Comm SEND ridx [B l ty lty] ** Send ridx prf)
    synth rs fs ts (Send r l ty k) | (Yes ridx) | (No no)
      = No (\case ((Comm SEND prf [B l _ ty]) ** (Send prf cont)) => no (ty ** cont))

  synth rs fs ts (Send r l ty k) | (No no)
    = No (\case ((Comm SEND prf [B l bty ty]) ** (Send prf cont)) => no (_ ** prf))

synth rs fs ts (Recv r xs) with (index rs r)
  synth rs fs ts (Recv r xs) | (Yes (n ** idx)) with (synth rs fs ts xs)
    synth rs fs ts (Recv r xs) | (Yes (n ** idx)) | (Yes (fst ** snd))
      = Yes (Comm RECV _ fst ** Recv idx snd)

    synth rs fs ts (Recv r xs) | (Yes (n ** idx)) | (No no)
      = No (\case (((Comm RECV x tys) ** (Recv x bs))) => no (tys ** bs))
  synth rs fs ts (Recv r xs) | (No no)
    = No (\case ((Comm RECV idx tys) ** (Recv idx bs)) => no (_ ** idx))

synth rs fs ts (If c tt ff) with (check ts BOOL c)
  synth rs fs ts (If c tt ff) | (Yes cond) with (synth rs fs ts tt)
    synth rs fs ts (If c tt ff) | (Yes cond) | (Yes (tyL ** pL)) with (synth rs fs ts ff)
      synth rs fs ts (If c tt ff) | (Yes cond) | (Yes (tyL ** pL)) | (Yes (tyR ** pR)) with (merge tyL tyR)
        synth rs fs ts (If c tt ff) | (Yes cond) | (Yes (tyL ** pL)) | (Yes (tyR ** pR)) | (Yes (ty ** prf))
          = Yes (ty ** If tyL tyR cond pL pR prf)
        synth rs fs ts (If c tt ff) | (Yes cond) | (Yes (tyL ** pL)) | (Yes (tyR ** pR)) | (No no)
          = No (mergeFails pL pR no)

--          (\case (fst ** (If tyL tyR x y z prf)) => no (fst ** ?condMerge))

      synth rs fs ts (If c tt ff) | (Yes cond) | (Yes (tyL ** pL)) | (No no)
        = No (\case (fst ** (If _ _ _ y z _)) => no (_ ** z))
    synth rs fs ts (If c tt ff) | (Yes cond) | (No no)
      = No (\case (fst ** (If _ _ x_ y z _)) => no (_ ** y))

  synth rs fs ts (If c tt ff) | (No no)
    = No (\case (fst ** (If _ _ cond x y prf)) => no cond)

synth rs fs ts (The tytm tm) with (synth rs fs tytm)
  synth rs fs ts (The tytm tm) | (Yes (ty ** pTT)) with (check rs fs ts ty tm)
    synth rs fs ts (The tytm tm) | (Yes (ty ** pTT)) | (Yes tm')
      = Yes (ty ** The pTT tm')

    synth rs fs ts (The tytm tm) | (Yes (ty ** pTT)) | (No no)
      = No (checkFails pTT no)

  synth rs fs ts (The tytm tm) | (No no)
    = No (\case (fst ** (The x y)) => no (fst ** x))

check rs fs ts ty (Switch tm) with (synth rs fs ts tm)
  check rs fs ts ty (Switch tm) | (Yes (tySyn ** prf)) with (subset tySyn ty)
    check rs fs ts ty (Switch tm) | (Yes (tySyn ** prf)) | (Yes prfS)
      = Yes (Switch tySyn prf prfS)
    check rs fs ts ty (Switch tm) | (Yes (tySyn ** prf)) | (No no)
      = No (\case (Switch ty x y) => no ?checkSynSubset)
  check rs fs ts ty (Switch tm) | (No no)
    = No (\case (Switch ty x y) => no (_ ** x))

namespace Session
  public export
  data Check : (rs : SnocList Role)
            -> (ts : SnocList (String,Base))
            -> (tm : Session.AST)
                  -> Type
    where
      Session : Local rs Lin tmty tyExp
             -> Synth rs Lin ts tm tySyn
             -> Subset tySyn tyExp
             -> Check rs ts (Session tmty tm)
             -- here we can do projection...



-- [ EOF ]
