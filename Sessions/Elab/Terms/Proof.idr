module Sessions.Elab.Terms.Proof

import Sessions.Types.Local
import Sessions.Types.Local.Subset
import Sessions.Types.Local.Merge.Synthesis
import Sessions.AST

import Sessions.Elab.Expr
import Sessions.Elab.Local

import Sessions.Elab.Terms.Core
import Sessions.Elab.Terms.Unique

%default total

mutual
  namespace Branches

    export
    synth : (rs : SnocList Role)
         -> (fs : SnocList (Fix))
         -> (ts : SnocList (String,Base))
         -> (bs  : List (String, Base))
         -> (tms : List (String, String, Synth.AST))
                -> Dec (DPair (List (Branch rs fs))
                              (Synth rs fs ts bs tms))

  namespace Cases
    export
    synth : (rs : SnocList Role)
         -> (fs : SnocList (Fix))
         -> (ts : SnocList (String,Base))
         -> (bs  : List (String, Base))
         -> (tms : List (String, String, Synth.AST))
                -> Dec (DPair (List (Local rs fs))
                              (Synth rs fs ts bs tms))

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

    notCoveringLeft : DPair (List (Branch rs fs)) (Synth rs fs ts (x :: xs) []) -> Void
    notCoveringLeft (_ ** pat) = void (absurd pat)

    notCoveringRight : DPair (List (Branch rs fs)) (Synth rs fs ts [] (x :: xs)) -> Void
    notCoveringRight (_ ** pat) = void (absurd pat)

    synth rs fs ts [] []
      = Yes ([] ** End)

    synth rs fs ts [] (x :: xs)
      = No notCoveringRight

    synth rs fs ts (x :: xs) []
      = No notCoveringLeft
    synth rs fs ts ((lx, b) :: xs) ((ly,v,k) :: ys) with (Equality.decEq lx ly)
      synth rs fs ts ((lx, b) :: xs) ((ly,v,k) :: ys) | (No no)
         = No $ \case ((fst ** snd)) => case snd of
                                            (Ext x y) => no Refl

      synth rs fs ts ((l, b) :: xs) ((l,v,k) :: ys) | (Yes Refl) with (synth rs fs (ts :< (v,b)) k)
        synth rs fs ts ((l, b) :: xs) ((l,v,k) :: ys) | (Yes Refl) | (No no)
          = No (\case ((B l b ty :: tys) ** (Ext x y)) => no (ty ** x))

        synth rs fs ts ((l, b) :: xs) ((l,v,k) :: ys) | (Yes Refl) | (Yes (ty ** tm)) with (Branches.synth rs fs ts xs ys)
          synth rs fs ts ((l, b) :: xs) ((l,v,k) :: ys) | (Yes Refl) | (Yes (ty ** tm)) | (No no)
            = No (\case ((B l b ty :: tys) ** (Ext x y)) => no (tys ** y))

          synth rs fs ts ((l, b) :: xs) ((l,v,k) :: ys) | (Yes Refl) | (Yes (ty ** tm)) | (Yes (tys ** tms))
            = Yes (B l b ty :: tys ** Ext tm tms)


  namespace Cases

    notCoveringLeft : DPair (List (Local rs fs)) (Synth rs fs ts (x :: xs) []) -> Void
    notCoveringLeft (_ ** pat) = void (absurd pat)

    notCoveringRight : DPair (List (Local rs fs)) (Synth rs fs ts [] (x :: xs)) -> Void
    notCoveringRight (_ ** pat) = void (absurd pat)

    synth rs fs ts [] []
      = Yes ([] ** End)

    synth rs fs ts [] (x :: xs)
      = No notCoveringRight
    synth rs fs ts (x :: xs) []
      = No notCoveringLeft

    synth rs fs ts ((lx,b) :: xs) ((ly,v,k) :: ys) with (Equality.decEq lx ly)
      synth rs fs ts ((lx,b) :: xs) ((ly,v,k) :: ys) | (No no)
        = No $ \case ((fst ** snd)) => case snd of
                                            (Ext x y) => no Refl

      synth rs fs ts ((l, b) :: xs) ((l,v,k) :: ys) | (Yes Refl) with (synth rs fs (ts :< (v,b)) k)
        synth rs fs ts ((l, b) :: xs) ((l,v,k) :: ys) | (Yes Refl) | (No no)
          = No (\case ((ty :: tys) ** (Ext x y)) => no (ty ** x))

        synth rs fs ts ((l, b) :: xs) ((l,v,k) :: ys) | (Yes Refl) | (Yes (ty ** tm)) with (Cases.synth rs fs ts xs ys)
          synth rs fs ts ((l, b) :: xs) ((l,v,k) :: ys) | (Yes Refl) | (Yes (ty ** tm)) | (No no)
            = No (\case ((ty :: tys) ** (Ext x y)) => no (tys ** y))

          synth rs fs ts ((l, b) :: xs) ((l,v,k) :: ys) | (Yes Refl) | (Yes (ty ** tm)) | (Yes (tys ** tms))
            = Yes (ty :: tys ** Ext tm tms)



  mergeFails : Synth rs fs ts tt tyL
            -> Synth rs fs ts ff tyR
            -> (DPair (Local rs fs) (Merge tyL tyR) -> Void)
            -> DPair (Local rs fs) (Synth rs fs ts (If c tt ff)) -> Void
  mergeFails px py f (fst ** (If cond pl pr prf)) with (unique px pl)
    mergeFails px py f (fst ** (If cond pl pr prf)) | Refl with (unique py pr)
      mergeFails px py f (fst ** (If cond pl pr prf)) | Refl | Refl = f (fst ** prf)

  checkSwitchFails : (no : tySyn === ty -> Void)
                  -> Synth rs fs ts tm tySyn
                  -> Check rs fs ts ty (Switch tm) -> Void
  checkSwitchFails no x (Switch y Refl) with (unique x y)
    checkSwitchFails no x (Switch y Refl) | Refl = no Refl

  isNatSumExp : DPair (Local rs fs) (Synth rs fs ts (Recv r NAT xs)) -> Void
  isNatSumExp (_ ** pat) = void (absurd pat)

  isBoolSumExp : DPair (Local rs fs) (Synth rs fs ts (Recv r BOOL xs)) -> Void
  isBoolSumExp (_ ** pat) = void (absurd pat)

  matchRequiresSum : (IsSum ty -> Void) -> Expr ts m ty -> DPair (Local rs fs) (Synth rs fs ts (Match m cs)) -> Void
  matchRequiresSum f x (fst ** Match tm bs prf) {ty} with (unique x tm)
    matchRequiresSum f x (fst ** Match tm bs prf) {ty = (SUM xs)} | Refl = f YIS

  matchScrutineeFails : (DPair Base (Expr ts m) -> Void) -> DPair (Local rs fs) (Synth rs fs ts (Match m cs)) -> Void
  matchScrutineeFails f ((fst ** (Match tm bs prf))) = f (_ ** tm)

  casesFail : (DPair (List (Local rs fs)) (Synth rs fs ts xs cs) -> Void) -> Expr ts m (SUM xs) -> DPair (Local rs fs) (Synth rs fs ts (Match m cs)) -> Void
  casesFail f x (fst ** (Match tm bs prf)) with (unique x tm)
    casesFail f x (fst ** (Match tm bs prf)) | Refl = f (_ ** bs)

  matchMergesFail : (DPair (Local rs fs) (Merges Merge tys) -> Void) -> Expr ts m (SUM xs) -> Synth rs fs ts xs cs tys -> DPair (Local rs fs) (Synth rs fs ts (Match m cs)) -> Void
  matchMergesFail f m cs (fst ** (Match tm bs prf)) with (unique m tm)
    matchMergesFail f m cs (fst ** (Match tm bs prf)) | Refl with (uniques cs bs)
      matchMergesFail f m cs (fst ** (Match tm bs prf)) | Refl | Refl = f (fst ** prf)

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

  synth rs fs ts (Send r l v k) with (index rs r)
    synth rs fs ts (Send r l v k) | (Yes (n ** idx)) with (synth ts v)
      synth rs fs ts (Send r l v k) | (Yes (n ** idx)) | (Yes (ty ** prf)) with (synth rs fs ts k)
        synth rs fs ts (Send r l v k) | (Yes (n ** idx)) | (Yes (ty ** prf)) | (Yes (lty ** prfL))
          = Yes (Comm SEND idx [B l ty lty] ** Send idx prf prfL)
        synth rs fs ts (Send r l v k) | (Yes (n ** idx)) | (Yes (ty ** prf)) | (No no)
          = No $ \case ((Comm SEND x [B l b ty]) ** (Send x pe cont)) => no (ty ** cont)
      synth rs fs ts (Send r l v k) | (Yes (n ** idx)) | (No no)
        = No $ \case ((Comm SEND prf [B l b ty]) ** (Send prf pe cont)) => no (b ** pe)
    synth rs fs ts (Send r l v k) | (No no)
      = No (\case ((Comm SEND prf [B l b ty]) ** (Send prf _ _)) => no (_ ** prf))

  synth rs fs ts (Recv r ty xs) with (index rs r)
    synth rs fs ts (Recv r NAT xs) | (Yes (n ** idx))
      = No (isNatSumExp)
    synth rs fs ts (Recv r BOOL xs) | (Yes (n ** idx))
      = No isBoolSumExp

    synth rs fs ts (Recv r (SUM ys) xs) | (Yes (n ** idx)) with (Branches.synth rs fs ts ys xs)
      synth rs fs ts (Recv r (SUM ys) xs) | (Yes (n ** idx)) | (Yes (ls ** prf))
        = Yes (Comm RECV _ ls ** Recv idx prf)
      synth rs fs ts (Recv r (SUM ys) xs) | (Yes (n ** idx)) | (No no)
        = No (\case (((Comm RECV x tys) ** (Recv x bs))) => no (tys ** bs))

    synth rs fs ts (Recv r bs xs) | (No no)
      = No $ \case (fst ** snd) => case snd of
                                        (Recv idx x) => no (_ ** idx)

  synth rs fs ts (The tytm tm) with (synth rs fs tytm)
    synth rs fs ts (The tytm tm) | (Yes (ty ** pTT)) with (check rs fs ts ty tm)
      synth rs fs ts (The tytm tm) | (Yes (ty ** pTT)) | (Yes tm')
        = Yes (ty ** The pTT tm')

      synth rs fs ts (The tytm tm) | (Yes (ty ** pTT)) | (No no)
        = No (checkFails pTT no)

    synth rs fs ts (The tytm tm) | (No no)
      = No (\case (fst ** (The x y)) => no (fst ** x))

  synth rs fs ts (If c tt ff) with (check ts BOOL c)
    synth rs fs ts (If c tt ff) | (Yes cond) with (synth rs fs ts tt)
      synth rs fs ts (If c tt ff) | (Yes cond) | (Yes (tyL ** pL)) with (synth rs fs ts ff)
        synth rs fs ts (If c tt ff) | (Yes cond) | (Yes (tyL ** pL)) | (Yes (tyR ** pR)) with (merge tyL tyR)
          synth rs fs ts (If c tt ff) | (Yes cond) | (Yes (tyL ** pL)) | (Yes (tyR ** pR)) | (Yes (ty ** prf))
            = Yes (ty ** If cond pL pR prf)
          synth rs fs ts (If c tt ff) | (Yes cond) | (Yes (tyL ** pL)) | (Yes (tyR ** pR)) | (No no)
            = No (mergeFails pL pR no)

        synth rs fs ts (If c tt ff) | (Yes cond) | (Yes (tyL ** pL)) | (No no)
          = No (\case (fst ** (If  _ y z _)) => no (_ ** z))
      synth rs fs ts (If c tt ff) | (Yes cond) | (No no)
        = No (\case (fst ** (If x_ y z _)) => no (_ ** y))

    synth rs fs ts (If c tt ff) | (No no)
      = No (\case (fst ** (If cond x y prf)) => no cond)


  synth rs fs ts (Match m cs) with (synth ts m)
    synth rs fs ts (Match m cs) | (Yes (ty ** val)) with (isSum ty)
      synth rs fs ts (Match m cs) | (Yes (ty ** val)) | (Yes prf) with (ty)
        synth rs fs ts (Match m cs) | (Yes (ty ** val)) | (Yes YIS) | (SUM xs) with (Cases.synth rs fs ts xs cs)
          synth rs fs ts (Match m cs) | (Yes (ty ** val)) | (Yes YIS) | (SUM xs) | (Yes (tys ** prf)) with (Synthesis.merges tys)
            synth rs fs ts (Match m cs) | (Yes (ty ** val)) | (Yes YIS) | (SUM xs) | (Yes (tys ** prf)) | (Yes (fst ** snd))
              = Yes (fst ** Match val prf snd)
            synth rs fs ts (Match m cs) | (Yes (ty ** val)) | (Yes YIS) | (SUM xs) | (Yes (tys ** prf)) | (No no)
              = No (matchMergesFail no val prf)
          synth rs fs ts (Match m cs) | (Yes (ty ** val)) | (Yes YIS) | (SUM xs) | (No no)
            = No (casesFail no val)

      synth rs fs ts (Match m cs) | (Yes (ty ** val)) | (No no)
        = No (matchRequiresSum no val)

    synth rs fs ts (Match m cs) | (No no)
      = No (matchScrutineeFails no)

  -- [ Note ] Checking is here

  check rs fs ts ty (Switch tm) with (synth rs fs ts tm)
    check rs fs ts ty (Switch tm) | (Yes (tySyn ** prf)) with (decEq tySyn ty)
      check rs fs ts ty (Switch tm) | (Yes (ty ** prf)) | (Yes Refl)
        = Yes (Switch prf Refl)
      check rs fs ts ty (Switch tm) | (Yes (tySyn ** prf)) | (No no)
        = No (checkSwitchFails no prf)
    check rs fs ts ty (Switch tm) | (No no)
      = No (\case (Switch x y) => no (_ ** x))

-- [ EOF ]
