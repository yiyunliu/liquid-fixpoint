{- | This module creates new bindings for each argument of each kvar.
     It also makes sure that all arguments to each kvar are explicit.

     For example,

```
bind 0 x
bind 1 v
constraint:
  env [0; 1]
  rhs $k_42 // implicit substitutions [x:=x], [v:=v]
wf:
  env [0]
  reft {v : int | [$k_42]}
```

becomes

```
bind 0 x
bind 1 v
bind 2 lq_karg$x$k_42
constraint:
  env [0; 1]
  rhs $k_42[lq_karg$x$k_42:=x][lq_karg$v$k_42:=v]

wf:
  env [2]
  reft {lq_karg$v$k_42 : int | [$k_42]}
```

-}

module Language.Fixpoint.Solver.UniqifyKVars (wfcUniqify) where

import           Language.Fixpoint.Types
import           Language.Fixpoint.Types.Visitor (mapKVarSubsts)
import qualified Data.HashMap.Strict as M
import           Data.Foldable       (foldl')

--------------------------------------------------------------------------------
wfcUniqify    :: SInfo s a -> SInfo s a
wfcUniqify fi = updateWfcs $ remakeSubsts fi



-- mapKVarSubsts (\k su -> restrict table k su xs)
--------------------------------------------------------------------------------
remakeSubsts :: SInfo s a -> SInfo s a
--------------------------------------------------------------------------------
remakeSubsts fi = mapKVarSubsts (remakeSubst fi) fi

remakeSubst :: SInfo s a -> KVar s -> Subst s -> Subst s
remakeSubst fi k su = foldl' (updateSubst k) su (kvarDomain fi k)

updateSubst :: KVar s -> Subst s -> FixSymbol -> Subst s
updateSubst k (Su su) sym
  = case M.lookup sym su of
      Just z  -> Su $ M.delete sym $ M.insert ksym z          su
      Nothing -> Su $                M.insert ksym (eVar sym) su
    where
      kx      = kv k
      ksym    = kArgSymbol sym kx

-- / | sym `M.member` su = Su $ M.delete sym $ M.insert ksym (su M.! sym) su
-- /  | otherwise         = Su $                M.insert ksym (eVar sym)   su

--------------------------------------------------------------------------------
updateWfcs :: SInfo s a -> SInfo s a
--------------------------------------------------------------------------------
updateWfcs fi = M.foldl' updateWfc fi (ws fi)

updateWfc :: SInfo s a -> WfC s a -> SInfo s a
updateWfc fi w    = fi'' { ws = M.insert k w' (ws fi) }
  where
    w'            = updateWfCExpr (subst su) w''
    w''           = w { wenv = insertsIBindEnv newIds mempty, wrft = (v', t, k) }
    (_, fi'')     = newTopBind v' (trueSortedReft t) fi'
    (fi', newIds) = foldl' (accumBindsIfValid k) (fi, []) (elemsIBindEnv $ wenv w)
    (v, t, k)     = wrft w
    v'            = kArgSymbol v (kv k)
    su            = mkSubst ((v, EVar v'):[(x, eVar $ kArgSymbol x (kv k)) | x <- kvarDomain fi k])

accumBindsIfValid :: KVar s -> (SInfo s a, [BindId]) -> BindId -> (SInfo s a, [BindId])
accumBindsIfValid k (fi, ids) i = if renamable then accumBinds k (fi, ids) i else (fi, i : ids)
  where
    (_, sr)                     = lookupBindEnv i      (bs fi)
    renamable                   = isValidInRefinements (sr_sort sr)

accumBinds :: KVar s -> (SInfo s a, [BindId]) -> BindId -> (SInfo s a, [BindId])
accumBinds k (fi, ids) i = (fi', i' : ids)
  where
    (oldSym, sr) = lookupBindEnv i (bs fi)
    newSym       = {- tracepp "kArgSymbol" $ -}  kArgSymbol oldSym (kv k)
    (i', fi')    = newTopBind newSym sr fi

-- | `newTopBind` ignores the actual refinements as they are not relevant
--   in the kvar parameters (as suggested by BLC.)
newTopBind :: FixSymbol -> SortedReft s -> SInfo s a -> (BindId, SInfo s a)
newTopBind x sr fi = (i', fi {bs = be'})
  where
    (i', be')   = insertBindEnv x (top sr) (bs fi)

--------------------------------------------------------------

isValidInRefinements :: Sort s -> Bool
isValidInRefinements FInt        = True
isValidInRefinements FReal       = True
isValidInRefinements FNum        = False
isValidInRefinements FFrac       = False
isValidInRefinements (FObj _)    = True
isValidInRefinements (FVar _)    = True
isValidInRefinements (FFunc _ _) = False
isValidInRefinements (FAbs  _ t) = isValidInRefinements t
isValidInRefinements (FTC _)     = True --TODO is this true? seems to be required for e.g. ResolvePred.hs
isValidInRefinements (FApp _ _)  = True
