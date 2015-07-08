import Graphics.Element exposing (show)


type alias Id =
  Int


type alias Ctx =
  { lastId : Id
  , errors : List (Spec, Impl)
  }


type alias M a =
  Ctx -> (a, Ctx)


unit : a -> M a
unit v ctx = (v, ctx)


(*>) : M a -> (a -> M b) -> M b
(*>) first second ctx = first ctx |> uncurry second


lift : (a -> b -> c) -> (M a -> M b -> M c)
lift simple =
  \a -> \b ->
    a *> \x ->
      b *> \y ->
        unit (simple x y)


foldM : (a -> b -> b) -> M b -> List (M a) -> M b
foldM folder start list =
  List.foldl (lift folder) start list


newId : M Int
newId ctx =
  let id = ctx.lastId + 1 in
    (id, { ctx | lastId <- id })


error : (Spec, Impl) -> M Bool
error msg ctx =
  (False, { ctx | errors <- ctx.errors ++ [msg] })


mock : Spec -> M Impl
mock spec =
  case spec of
    Prim t ->
      unit <| IPrim t
    
    Pred p ->
      unit <| IPred p
    
    Conj list ->
      unit <| IList
        (List.map mock list)
    
    Disj list ->
      unit <| INondeterm
        (List.indexedMap (\i -> \o -> (i + 1, mock o)) list)
    
    Imp s1 s2 ->
      unit <| IFun (\arg ->
        check (s1, unit arg) *> \chk ->
          if chk then
            mock s2
          else
            unit IError)
    
    All typeC specC ->
      unit <| IFun (\arg ->
        case arg of
          IPrim t ->
            mock <| specC (Prim t)
          
          otherwise ->
            unit IError)
    
    Exists typeC specC ->
      newId *> \id ->
        let t = typeC id in
          unit <| IList [unit <| IPrim t, mock <| specC (Prim t)]


check : (Spec, M Impl) -> M Bool
check (spec, impl) =
  impl *> \impl ->
    case (spec, impl) of
      (Prim t, IPrim t) ->
        unit True
      
      (Pred t, IPred t) ->
        unit True
      
      (Conj lst, IList lst') ->
        if List.length lst == List.length lst' then
          List.map2 (,) lst lst' |>
            List.map check |>
              foldM (&&) (unit True)
        else
          error (spec, impl)
      
      (Disj lst, IOption (id, opt)) ->
        if id >= 1 && id <= List.length lst then
          case List.drop (id - 1) lst |> List.take 1 of
            [optSpec] ->
              check (optSpec, opt)
            
            otherwise ->
              error (spec, impl)
        else
          error (spec, impl)
      
      (Imp s1 s2, IFun fun) ->
        mock s1 *> fun *> \r ->
          check (s2, unit r)
      
      (All tc sc, IFun fun) ->
        newId *> \id ->
          let v = tc id in
            check (sc (Prim v), fun (IPrim v))
      
      (Exists tc sc, IList [mp, i]) ->
        mp *> \(IPrim t) ->
          check (sc (Prim t), i)
      
      (_, ICase (IOption (id, opt)) lst) ->
        if id >= 1 && id <= List.length lst then
          case List.drop (id - 1) lst |> List.take 1 of
            [caseImpl] ->
              check (spec, opt *> caseImpl)
            
            otherwise ->
              error (spec, impl)
        else
          error (spec, impl)
      
      (_, ICase (INondeterm optList) lst) ->
        if List.length lst == List.length optList then
          List.map2 (\(id, o) -> \c -> check (spec, o *> c)) optList lst |>
            foldM (&&) (unit True)
        else
          error (spec, impl)
      
      otherwise ->
        error (spec, impl)


type Spec
  = Error
  | Prim Type
  | Pred Predicate
  | Conj (List Spec)
  | Disj (List Spec)
  | Imp Spec Spec
  | All (Id -> Type) (Spec -> Spec)
  | Exists (Id -> Type) (Spec -> Spec)


type Impl
  = IError
  | IPrim Type
  | IPred Predicate
  | IList (List (M Impl))
  | IOption (Id, M Impl)
  | INondeterm (List (Id, M Impl)) -- non-deterministic option, for check only
  | ICase Impl (List (Impl -> M Impl))
  | IFun (Impl -> M Impl)


call mImpl arg =
  mImpl *> \(IFun fun) ->
    fun arg


func closure =
  unit <| IFun closure


list lst =
  unit <| IList lst


exists witness evidence =
  unit <| IList [unit witness, evidence]


type Type
  = Nat Id


type Predicate
  = Suc (Type, Type)


suc (x, y) =
  case (x, y) of
    (Prim (Nat x), Prim (Nat y)) ->
      Pred <| Suc (Nat x, Nat y)

    otherwise ->
      Error


spec =
  All Nat <| \x ->
    Conj [ Exists Nat <| \y -> suc (x, y)
         , Exists Nat <| \y -> suc (x, y)
         ]


axiom =
  All Nat <| \x ->
    Exists Nat <| \y -> suc (x, y)


axiom2 = All Nat <| \x -> suc (x, x)


theorem = Imp (Disj [axiom, axiom2]) spec


byhand =
  func <|
    \opt ->
      unit <| ICase opt
        [ \(IFun ax) ->
            func <| \x ->
              list [ax x, ax x]
        , \(IFun ax) ->
            func <| \x ->
              list [exists x (ax x), exists x (ax x)]
        ]


main = show <|
  check (theorem, byhand)
    { lastId = 0, errors = [] }
