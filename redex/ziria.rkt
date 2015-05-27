#lang racket
(require redex)

(provide Z types Zv Zred Zmach)

(define-language Z
  [e c ::= k
           x
           (unop e)
           (binop e e)
           (if e e e)
           (let x e e)
           (letfun f ((x : τ) ...) e e)
           (f e ...)
           (letref x e e)
           (deref x)
           (set x e)
           (return e)
           (bind x e e)
           (seq e e)
           take
           (emit e)
           (repeat e)
           (arr e e)
           (parr e e)]
  [k ::= ()
         true
         false
         number]
  [unop ::= -]
  [binop ::= !=
             =
             +
             -
             *
             div]
  [f x ::= variable-not-otherwise-mentioned]
  [α β γ ν τ ::= unit
                 bool
                 int]
  [ι (C τ)
     T]
  [κ (ST ι τ τ)]
  [ρ ::= τ
         (ref τ)]
  [σ ::= τ
         κ]
  [φ ::= ρ
         (→ (ρ ...) σ)]
  [Γ ::= ((x φ) ...)]
  [θ ::= τ
         (ref τ)
         κ
         (→ (ρ ...) σ)])

(define-metafunction Z
  lookup : x ((x any) ...) -> any or #f
  [(lookup x ())                            #f]
  [(lookup x ((x any)     (x_1 any_1) ...)) any]
  [(lookup x ((x_1 any_1) (x_2 any_2) ...)) (lookup x ((x_2 any_2) ...))])

(define-metafunction Z
  extend : x any ((x any) ...) -> ((x any) ...)
  [(extend x any ((x_1 any_1) ...)) ((x any) ,@(filter (lambda (bind) (not (eq? (car bind) (term x)))) (term ((x_1 any_1) ...))))])

(define-metafunction Z
  extends : ((x any) ...) ((x any) ...) -> ((x any) ...)
  [(extends ((x any) ...) ((x_1 any_1) ...)) ((x any) ... ,@(filter (lambda (bind) (not (member (car bind) (term (x ...))))) (term ((x_1 any_1) ...))))])

;;
;; All free ref vars used by an expression
;;
(define-metafunction Z
  ref-vars : e -> (x ...)
  [(ref-vars k)
   ()]
  [(ref-vars x)
   ()]
  [(ref-vars (unop e)) 
   (ref-vars e)]
  [(ref-vars (binop e_1 e_2))
   (∪ (ref-vars e_1) (ref-vars e_2))]
  [(ref-vars (if e_1 e_2 e_3))
   (∪ (ref-vars e_1) (ref-vars e_2) (ref-vars e_3))]
  [(ref-vars (let x e_1 e_2))
   (∪ (ref-vars e_1) (- (ref-vars e_2) (x)))]
  [(ref-vars (letfun f ((x : τ) ...) e_1 e_2))
   (∪ (diff (ref-vars e_1) (x...)) (diff (ref-vars e_2) (f)))]
  [(ref-vars (f e ...))
   (∪ (f) (ref-vars e) ...)]
  [(ref-vars (letref x e_1 e_2))
   (∪ (ref-vars e_1) (diff (ref-vars e_2) (x)))]
  [(ref-vars (deref x))
   (x)]
  [(ref-vars (set x e))
   (∪ (ref-vars e) (x))]
  [(ref-vars (return e))
   (ref-vars e)]
  [(ref-vars (bind x e_1 e_2))
   (∪ (ref-vars e_1) (diff (ref-vars e_2) (x)))]
  [(ref-vars (seq e_1 e_2))
   (∪ (ref-vars e_1) (ref-vars e_2))]
  [(ref-vars take)
   ()]
  [(ref-vars (emit e))
   (ref-vars e)]
  [(ref-vars (repeat e))
   (ref-vars e)]
  [(ref-vars (arr e_1 e_2))
   (∪ (ref-vars e_1) (ref-vars e_2))]
  [(ref-vars (parr e_1 e_2))
   (∪ (ref-vars e_1) (ref-vars e_2))])

(define-metafunction Z
  ∪ : (x ...) ... -> (x ...)
  [(∪ (x_1 ...) (x_2 ...) (x_3 ...) ...) (∪ (x_1 ... x_2 ...) (x_3 ...) ...)]
  [(∪ (x_1 ...)) ,(remove-duplicates (term (x_1 ...)))]
  [(∪) ()])

(define-metafunction Z
  ∩ : (x ...) (x ...) -> (x ...)
  [(∩ (x_1 ...) (x_2 ...)) ,(filter (lambda (x) (member x (term (x_1 ...)))) (term (x_2 ...)))]
  [(∩) ()])

(define-metafunction Z
  diff : (x ...) (x ...) -> (x ...)
  [(diff (x ...) ()) (x ...)]
  [(diff (x_1 ... x_2 x_3 ...) (x_2 x_4 ...))
   (diff (x_1 ... x_3 ...) (x_2 x_4 ...))
   (side-condition (not (memq (term x_2) (term (x_3 ...)))))]
  [(diff (x_1 ...) (x_2 x_3 ...))
   (diff (x_1 ...) (x_3 ...))])

(define-metafunction Z
  ∈ : x (x ...) -> #t or #f
  [(∈ x   ())          #f]
  [(∈ x_1 (x_1 x ...)) #t]
  [(∈ x_1 (x_2 x ...)) (∈ x_1 (x ...))])

(define-judgment-form
  Z
  #:mode (base-type O)
  #:contract (base-type τ)
  
  [----------------
   (base-type unit)]
  
  [----------------
   (base-type bool)]
  
  [---------------
   (base-type int)])

(define-judgment-form
  Z
  #:mode (types I I O)
  #:contract (types Γ e θ)
  
  ;;
  ;; Base language rules
  ;;
  
  [----------------- "T-Unit"
   (types Γ () unit)]
  
  [------------------- "T-True"
   (types Γ true bool)]
  
  [-------------------- "T-False"
   (types Γ false bool)]
  
  [-------------------- "T-Int"
   (types Γ number int)]
  
  [(where θ (lookup x Γ))
   ---------------------- "T-Var"
   (types Γ x θ)]
  
  [(types Γ e_1 θ_1)
   (where (θ_1 θ_2) (unop-type unop))
   ---------------------------------- "T-Unop"
   (types Γ (unop e_1) θ_2)]
  
  [(types Γ e_1 θ_1)
   (types Γ e_2 θ_2)
   (where (θ_1 θ_2 θ_3) (binop-type binop))
   ---------------------------------------- "T-Binop"
   (types Γ (binop e_1 e_2) θ_3)]
  
  [(types Γ e_1 bool)
   (types Γ e_2 θ) (types Γ e_3 θ)
   ------------------------------- "T-If"
   (types Γ (if e_1 e_2 e_3) θ)]
  
  [(types Γ e_1 τ_1)
   (types ((x τ_1) . Γ) e_2 θ)
   --------------------------- "T-Let"
   (types Γ (let x e_1 e_2) θ)]
  
  [(types ((x ρ) ... . Γ) e_1 σ)
   (types ((f (→ (ρ ...) σ)) . Γ) e_2 θ)
   ------------------------------------------- "T-LetFun"
   (types Γ (letfun f (x : ρ ...) e_1 e_2) θ)]
  
  [(types Γ f (→ (ρ ..._1) σ))
   (types Γ e ρ) ...
   --------------------- "T-Call"
   (types Γ (f e ..._1) σ)]
  
  ;;
  ;; Computation languages rules
  ;;
  
  [(types Γ e_1 τ_1)
   (types ((x (ref τ_1)) . Γ) e_2 (ST ι α β))
   ------------------------------------------- "T-LetRef"
   (types Γ (letref x e_1 e_2) (ST ι α β))]
  
  [(types Γ x (ref τ)) (base-type α) (base-type β)
   ----------------------------------------------- "T-Deref"
   (types Γ (deref x) (ST (C τ) α β))]
  
  [(types Γ x (ref τ)) (types Γ e τ)
   (base-type α) (base-type β)
   ------------------------------------- "T-Set"
   (types Γ (set x e) (ST (C unit) α β))]
  
  [(types Γ e τ) (base-type α) (base-type β)
   ----------------------------------------- "T-Return"
   (types Γ (return e) (ST (C τ) α β))]
  
  [(types Γ c_1 (ST (C ν) α β)) (types ((x ν) . Γ) c_2 (ST ι α β))
   ----------------------------------------------------------------- "T-Bind"
  (types Γ (bind x c_1 c_2) (ST ι α β))]
  
  [(types Γ c_1 (ST (C ν) α β)) (types Γ c_2 (ST ι α β))
   ----------------------------------------------------- "T-Seq"
   (types Γ (seq c_1 c_2) (ST ι α β))]
  
  [(base-type α) (base-type β)
   ----------------------------- "T-Take"
   (types Γ take (ST (C α) α β))]
  
  [(types Γ e β) (base-type α)
   ------------------------------------ "T-Emit"
   (types Γ (emit e) (ST (C unit) α β))]
  
  [(types Γ c (ST (C unit) α β))
   ------------------------------- "T-Repeat"
   (types Γ (repeat c) (ST T α β))]
  
  [(types Γ c_1 (ST ι_1 α β)) (types Γ c_2 (ST ι_2 β γ))
   (where ι_3 (join ι_1 ι_2))
   ----------------------------------------------------- "T-Arr"
   (types Γ (arr c_1 c_2) (ST ι_3 α γ))]
  
  [(where (Γ_1 Γ_2) (split-Γ Γ c_1 c_2))
   (types Γ_1 c_1 (ST ι_1 α β)) (types Γ_2 c_2 (ST ι_2 β γ))
   (where ι_3 (join ι_1 ι_2))
   ----------------------------------------------------------- "T-PArr"
   (types Γ (parr c_1 c_2) (ST ι_3 α γ))])

(define-metafunction Z
  unop-type : unop -> (θ θ)
  [(unop-type -) (int int)])

(define-metafunction Z
  binop-type : binop -> (θ θ θ)
  [(binop-type =)   (int int bool)]
  [(binop-type !=)  (int int bool)]
  [(binop-type +)   (int int int)]
  [(binop-type -)   (int int int)]
  [(binop-type *)   (int int int)]
  [(binop-type div) (int int int)])

(define-metafunction Z
  join : ι ι -> ι
  [(join (C ν) T) (C ν)]
  [(join T (C ν)) (C ν)]
  [(join T T)     T])

(define-metafunction Z
  split-Γ : Γ e e -> (Γ Γ)
  [(split-Γ () e_1 e_2)
   (() ())]
  [(split-Γ ((x_1 (ref τ_1)) (x φ) ...) e_1 e_2)
   (((x_1 (ref τ_1)) . Γ_1) Γ_2)
   (where (Γ_1 Γ_2) (split-Γ ((x φ) ...) e_1 e_2))
   (side-condition (term (∈ x_1 (ref-vars e_1))))]
  [(split-Γ ((x_1 (ref τ_1)) (x φ) ...) e_1 e_2)
   (Γ_1 ((x_1 (ref τ_1)) . Γ_2))
   (where (Γ_1 Γ_2) (split-Γ ((x φ) ...) e_1 e_2))
   (side-condition (term (∈ x_1 (ref-vars e_2))))]
  [(split-Γ ((x_1 (ref τ_1)) (x φ) ...) e_1 e_2)
   (Γ_1 Γ_2)
   (where (Γ_1 Γ_2) (split-Γ ((x φ) ...) e_1 e_2))]
  [(split-Γ ((x_1 φ_1) (x φ) ...) e_1 e_2)
   (((x_1 φ_1) . Γ_1) (((x_1 φ_1) . Γ_2)))
   (where (Γ_1 Γ_2) (split-Γ ((x φ) ...) e_1 e_2))])

(define-extended-language Zv Z
  [E ::= (unop E)
         (binop E e)
         (binop v E)
         (if E e e)
         (let x E e)
         (f v ... E e ...)
         (letref x E e)
         (set x E)
         (return E)
         (bind x E e)
         (seq E e)
         (emit E)
         hole]
  ;; Locations
  [l ::= variable-not-otherwise-mentioned]
  ;; Queue locations
  [q ::= variable-not-otherwise-mentioned]
  ;; Values
  [v  ::= k]
  ;; Closures
  [clo ::= ((x ...) e)]
  ;; "Store" values. These are either values, heap locations, or closures.
  [vσ ::= v
          l
          clo]
  ;; Store
  [Σ ::= ((x vσ) ...)]
  ;; Heap
  [H ::= ((l v) ...)]
  ;; Actions
  [δ ::= tick
         wait
         (cons v)
         (yield v)]
  ;; Threads
  [t ::= (thread Σ H e δ)]
  ;; Queues
  [Q I O ::= (queue v ...)
             mvar
             (mvar v)]
  ;; Process
  [p ::= (proc t q_1 q_2)]
  ;; Queue heap
  [Φ ::= ((q Q) ...)]
  ;; Machines
  [m ::= (mach Φ (p ...))]
  )

(define Zred
  (reduction-relation
   Zv
   #:domain t
   [--> (in-hole (thread Σ H E tick) x)
        (in-hole (thread Σ H E tick) v)
        (where v (lookup x Σ))
        "E-Var"]
   
   [--> (in-hole (thread Σ H E tick) (unop number))
        (in-hole (thread Σ H E tick) (meta-unop unop number))
        "E-Unop"]
   
   [--> (in-hole (thread Σ H E tick) (binop number_1 number_2))
        (in-hole (thread Σ H E tick) (meta-binop binop number_1 number_2))
        "E-Binop"]
   
   [--> (in-hole (thread Σ H E tick) (if true e_1 e_2))
        (in-hole (thread Σ H E tick) e_1)
        "E-IfTrue"]
   
   [--> (in-hole (thread Σ H E tick) (if false e_1 e_2))
        (in-hole (thread Σ H E tick) e_2)
        "E-IfFalse"]
   
   [--> (in-hole (thread Σ_1 H E tick) (let x v e))
        (in-hole (thread Σ_2 H E tick) e)
        (where Σ_2 (extend x v Σ_1))
        "E-Let"]
   
   [--> (in-hole (thread Σ_1 H E tick) (letfun f ((x : τ) ...) e_1 e_2))
        (in-hole (thread Σ_2 H E tick) e_2)
        (where Σ_2 (extend f ((x ...) e_1) Σ_1))
        "E-LetFun"]
   
   [--> (in-hole (thread Σ_1 H E tick) (f v ..._1))
        (in-hole (thread Σ_2 H E tick) e)
        (where ((x ..._1) e) (lookup f Σ_1))
        (where Σ_2 (extends ((x v) ...) Σ_1))
        "E-Call"]
   
   [--> (in-hole (thread Σ_1 H_1 E tick) (letref x v e))
        (in-hole (thread Σ_2 H_2 E tick) e)
        (where l ,(variable-not-in (term H_1) 'l))
        (where Σ_2 (extend x l Σ_1))
        (where H_2 (extend l v H_1))
        "E-LetRef"]
   
   [--> (in-hole (thread Σ H E tick) (deref x))
        (in-hole (thread Σ H E tick) (return v))
        (where l (lookup x Σ))
        (where v (lookup l H))
        "E-Deref"]
   
   [--> (in-hole (thread Σ H_1 E tick) (set x v))
        (in-hole (thread Σ H_2 E tick) (return ()))
        (where l (lookup x Σ))
        (where H_2 (extend l v H_1))
        "E-Set"]
   
   [--> (in-hole (thread Σ_1 H E tick) (bind x (return v) e))
        (in-hole (thread Σ_2 H E tick) e)
        (where Σ_2 (extend x v Σ_1))
        "E-Bind"]
   
   [--> (in-hole (thread Σ H E tick) (seq (return v) e_2))
        (in-hole (thread Σ H E tick) e_2)
        (fresh x)
        "E-Seq"]
   
   [--> (in-hole (thread Σ H E tick) take)
        (in-hole (thread Σ H E wait) take)
        "E-TakeWait"]
   
   [--> (in-hole (thread Σ H E (cons v)) take)
        (in-hole (thread Σ H E tick)     (return v))
        "E-TakeConsume"]
   
   [--> (in-hole (thread Σ H E tick)      (emit v))
        (in-hole (thread Σ H E (yield v)) (return ()))
        "E-Emit"]
   
   [--> (in-hole (thread Σ H E tick) (repeat e))
        (in-hole (thread Σ H E tick) (seq e (repeat e)))
        "E-Repeat"]))

(define-metafunction Zv
  [(meta-unop - number) ,(apply - (term (number)))])

(define-metafunction Zv
  [(meta-binop =   number   number)   true]
  [(meta-binop =   number_1 number_2) false]
  [(meta-binop !=  number   number)   false]
  [(meta-binop !=  number_1 number_2) true]
  [(meta-binop +   number_1 number_2) ,(apply + (term (number_1 number_2)))]
  [(meta-binop -   number_1 number_2) ,(apply - (term (number_1 number_2)))]
  [(meta-binop *   number_1 number_2) ,(apply * (term (number_1 number_2)))]
  [(meta-binop div number_1 number_2) ,(apply quotient (term (number_1 number_2)))])

(define-metafunction Zv
  split-Σ : Σ e e -> (Σ Σ)
  [(split-Σ () e_1 e_2)
   (() ())]
  [(split-Σ ((x_1 l_1) (x vσ) ...) e_1 e_2)
   (((x_1 l_1) . Σ_1) Σ_2)
   (where (Σ_1 Σ_2) (split-Σ ((x vσ) ...) e_1 e_2))
   (side-condition (term (∈ x_1 (ref-vars e_1))))]
  [(split-Σ ((x_1 l_1) (x vσ) ...) e_1 e_2)
   (Σ_1 ((x_1 l_1) . Σ_2))
   (where (Σ_1 Σ_2) (split-Σ ((x vσ) ...) e_1 e_2))
   (side-condition (term (∈ x_1 (ref-vars e_2))))]
  [(split-Σ ((x_1 l_1) (x vσ) ...) e_1 e_2)
   (Σ_1 Σ_2)
   (where (Σ_1 Σ_2) (split-Σ ((x vσ) ...) e_1 e_2))]
  [(split-Σ ((x_1 vσ_1) (x vσ) ...) e_1 e_2)
   (((x_1 vσ_1) . Σ_1) (((x_1 vσ_1) . Σ_2)))
   (where (Σ_1 Σ_2) (split-Γ ((x vσ) ...) e_1 e_2))])

(define-judgment-form
  Zv
  #:mode (→z I O)
  #:contract (→z t t)
  
  [(where (t_1 ... t t_2 ...) ,(apply-reduction-relation Zred (term (thread Σ H e δ))))
   ------------------------------------------------------------------------------------
   (→z (thread Σ H e δ) t)])

(define Zmach
  (reduction-relation
   Zv
   #:domain m
   [--> (in-hole (mach Φ (p_1 ... (proc (thread Σ_1 H_1 E δ_1) q_1 q_2) p_2 ...)) e_1)
        (in-hole (mach Φ (p_1 ... (proc (thread Σ_2 H_2 E δ_2) q_1 q_2) p_2 ...)) e_2)
        (judgment-holds (→z (thread Σ_1 H_1 e_1 δ_1) (thread Σ_2 H_2 e_2 δ_2)))
        "P-Tick"]
   [--> (in-hole (mach Φ_1 (p_1 ... (proc (thread Σ H E wait)     q_1 q_2) p_2 ...)) e)
        (in-hole (mach Φ_2 (p_1 ... (proc (thread Σ H E (cons v)) q_1 q_2) p_2 ...)) e)
        (where (Φ_2 v) (dequeue Φ_1 q_1))
        "P-Consume"]
   [--> (in-hole (mach Φ_1 (p_1 ... (proc (thread Σ H E (yield v)) q_1 q_2) p_2 ...)) e)
        (in-hole (mach Φ_2 (p_1 ... (proc (thread Σ H E tick)      q_1 q_2) p_2 ...)) e)
        (where Φ_2 (enqueue Φ_1 q_2 v))
        "P-Yield"]
   [--> (mach ((q Q) ...)              (p_1 ... (proc (thread Σ H (arr e_1 e_2) tick) q_1 q_2) p_2 ...))
        (mach ((q_new mvar) (q Q) ...) (p_1 ... (proc (thread Σ H e_1 tick) q_1 q_new) (proc (thread Σ H e_2 tick) q_new q_2) p_2 ...))
        (fresh q_new)
        "P-Spawn"]
   [--> (mach ((q Q) ...)                 (p_1 ... (proc (thread Σ H (parr e_1 e_2) tick) q_1 q_2) p_2 ...))
        (mach ((q_new (queue)) (q Q) ...) (p_1 ... (proc (thread Σ_1 H e_1 tick) q_1 q_new) (proc (thread Σ_2 H e_2 tick) q_new q_2) p_2 ...))
        (fresh q_new)
        (where (Σ_1 Σ_2) (split-Σ Σ e_1 e_2))
        "P-ParSpawn"]))

(define-metafunction Zv
  dequeue : Φ q -> (Φ v) or #f
  [(dequeue ((q_1 Q_1) ... (q (queue v_1 v ...)) (q_2 Q_2) ...) q) (((q_1 Q_1) ... (q (queue v ...)) (q_2 Q_2) ...) v_1)]
  [(dequeue ((q_1 Q_1) ... (q (mvar v))          (q_2 Q_2) ...) q) (((q_1 Q_1) ... (q mvar)          (q_2 Q_2) ...) v)]
  [(dequeue Φ q) #f])

(define-metafunction Zv
  enqueue : Φ q v -> Φ or #f
  [(enqueue ((q_1 Q_1) ... (q (queue v_1 ...)) (q_2 Q_2) ...) q v) ((q_1 Q_1) ... (q (queue v_1 ... v)) (q_2 Q_2) ...)]
  [(enqueue ((q_1 Q_1) ... (q mvar)            (q_2 Q_2) ...) q v) ((q_1 Q_1) ... (q (mvar v))          (q_2 Q_2) ...)]
  [(enqueue Φ q v) #f])
