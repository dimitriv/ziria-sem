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
             <
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
  [μ (ST ι τ τ)]
  [ρ ::= τ
         (ref τ)]
  [σ ::= τ
         μ]
  [φ ::= ρ
         (→ (ρ ...) σ)]
  [Γ ::= ((x φ) ...)]
  [θ ::= τ
         (ref τ)
         μ
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

;;
;; Set union
;;
(define-metafunction Z
  ∪ : (x ...) ... -> (x ...)
  [(∪ (x_1 ...) (x_2 ...) (x_3 ...) ...) (∪ (x_1 ... x_2 ...) (x_3 ...) ...)]
  [(∪ (x_1 ...)) ,(remove-duplicates (term (x_1 ...)))]
  [(∪) ()])

;;
;; Set intersection
;;
(define-metafunction Z
  ∩ : (x ...) (x ...) -> (x ...)
  [(∩ (x_1 ...) (x_2 ...)) ,(filter (lambda (x) (member x (term (x_1 ...)))) (term (x_2 ...)))]
  [(∩) ()])

;;
;; Set difference
;;
(define-metafunction Z
  diff : (x ...) (x ...) -> (x ...)
  [(diff (x ...) ()) (x ...)]
  [(diff (x_1 ... x_2 x_3 ...) (x_2 x_4 ...))
   (diff (x_1 ... x_3 ...) (x_2 x_4 ...))
   (side-condition (not (memq (term x_2) (term (x_3 ...)))))]
  [(diff (x_1 ...) (x_2 x_3 ...))
   (diff (x_1 ...) (x_3 ...))])

;;
;; Set membership
;;
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
  [(binop-type <)   (int int bool)]
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
  ;; Continuations
  [κ ::= halt
         (popk Σ κ)
         (unopk unop κ)
         (binop1k binop e κ)
         (binop2k binop number κ)
         (ifk e e κ)
         (letk x e κ)
         (argk f (v ...) (e ...) κ)
         (letrefk x e κ)
         (setk x κ)
         (returnk κ)
         (bindk x e κ)
         (seqk e κ)
         (emitk κ)]
  ;; Locations
  [l ::= variable-not-otherwise-mentioned]
  ;; Queue locations
  [q ::= variable-not-otherwise-mentioned]
  ;; Values
  [v ::= k]
  ;; Closures
  [clo ::= ((x ...) e Σ)]
  ;; Store
  [Σ ::= ((x l) ...)]
  ;; Heap
  [H ::= ((l hv) ...)]
  ;; Heap values. These are either values or closures.
  [hv ::= v
          clo]
  ;; Actions
  [δ ::= tick
         wait
         (cons v)
         (yield v)]
  ;; Threads
  [t ::= (thread Σ H e κ δ)]
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
   [--> (thread Σ H x κ tick)
        (thread Σ H v κ tick)
        (where l (lookup x Σ))
        (where v (lookup l H))
        "E-Var"]
   
   [--> (thread Σ H (unop e) κ              tick)
        (thread Σ H e        (unopk unop κ) tick)
        "E-Unop"]
   
   [--> (thread Σ H (binop e_1 e_2) κ                    tick)
        (thread Σ H e_1            (binop1k binop e_2 κ) tick)
        "E-Binop"]
   
   [--> (thread Σ H (if e_1 e_2 e_3) κ               tick)
        (thread Σ H e_1              (ifk e_2 e_3 κ) tick)
        "E-If"]
   
   [--> (thread Σ H (let x e_1 e_2) κ              tick)
        (thread Σ H e_1             (letk x e_2 κ) tick)
        "E-Let"]
   
   [--> (thread Σ_1 H_1 (letfun f ((x : τ) ...) e_1 e_2) κ            tick)
        (thread Σ_2 H_2 e_2                              (popk Σ_1 κ) tick)
        (where l   ,(variable-not-in (term H_1) 'l))
        (where Σ_2 (extend f l Σ_1))
        (where H_2 (extend l ((x ...) e_1 Σ_2) H_1))
        "E-LetFun"]
   
   [--> (thread Σ H (f e_1 e_2 ...) κ                       tick)
        (thread Σ H e_1             (argk f () (e_2 ...) κ) tick)
        "E-Call"]
   
   [--> (thread Σ H (letref x e_1 e_2) κ                 tick)
        (thread Σ H e_1                (letrefk x e_2 κ) tick)
        "E-LetRef"]
   
   [--> (thread Σ H (deref x)  κ tick)
        (thread Σ H (return v) κ tick)
        (where l (lookup x Σ))
        (where v (lookup l H))
        "E-Deref"]
   
   [--> (thread Σ H (set x e) κ          tick)
        (thread Σ H e         (setk x κ) tick)
        "E-Set"]
   
   [--> (thread Σ H (return e) κ           tick)
        (thread Σ H e          (returnk κ) tick)
        (side-condition (not (redex-match Zv v (term e))))
        "E-Return"]
   
   [--> (thread Σ H (bind x e_1 e_2) κ               tick)
        (thread Σ H e_1              (bindk x e_2 κ) tick)
        "E-Bind"]
   
   [--> (thread Σ H (seq e_1 e_2) κ            tick)
        (thread Σ H e_1           (seqk e_2 κ) tick)
        "E-Seq"]
   
   [--> (thread Σ H take κ tick)
        (thread Σ H take κ wait)
        "E-TakeWait"]
   
   [--> (thread Σ H take       κ (cons v))
        (thread Σ H (return v) κ tick)
        "E-TakeConsume"]
   
   [--> (thread Σ H (emit e) κ         tick)
        (thread Σ H e        (emitk κ) tick)
        "E-Emit"]
   
   [--> (thread Σ H (repeat e)         κ tick)
        (thread Σ H (seq e (repeat e)) κ tick)
        "E-Repeat"]
   
   [--> (thread _ H v (popk Σ κ) tick)
        (thread Σ H v κ          tick)
        "E-PopK"]
   
   [--> (thread _ H (return v) (popk Σ κ) tick)
        (thread Σ H (return v) κ          tick)
        "E-PopReturnK"]
   
   [--> (thread Σ H number                  (unopk unop κ) tick)
        (thread Σ H (meta-unop unop number) κ              tick)
        "E-UnopK"]
   
   [--> (thread Σ H number (binop1k binop e κ)      tick)
        (thread Σ H e      (binop2k binop number κ) tick)
        "E-Binop1K"]
   
   [--> (thread Σ H number_2                             (binop2k binop number_1 κ) tick)
        (thread Σ H (meta-binop binop number_1 number_2) κ                          tick)
        "E-Binop2K"]
   
   [--> (thread Σ H true (ifk e_1 e_2 κ) tick)
        (thread Σ H e_1  κ               tick)
        "E-IfTrueK"]
   
   [--> (thread Σ H false (ifk e_1 e_2 κ) tick)
        (thread Σ H e_2   κ               tick)
        "E-IfFalseK"]
   
   [--> (thread Σ_1 H_1 v (letk x e κ) tick)
        (thread Σ_2 H_2 e (popk Σ_1 κ) tick)
        (where l   ,(variable-not-in (term H_1) 'l))
        (where Σ_2 (extend x l Σ_1))
        (where H_2 (extend l v H_1))
        "E-LetK"]
   
   [--> (thread Σ H v_2 (argk f (v_1 ...)     (e_1 e_2 ...) κ) tick)
        (thread Σ H e_1 (argk f (v_1 ... v_2) (e_2 ...) κ)     tick)
        "E-ArgK"]
   
   [--> (thread Σ_1 H_1 v_2 (argk f (v_1 ...) () κ) tick)
        (thread Σ_2 H_2 e_f (popk Σ_1 κ)            tick)
        (where (v ..._1) (v_1 ... v_2))
        (where (l ..._1) ,(variables-not-in (term H_1) (replicate (length (term (v ...))) 'l)))
        (where l_f (lookup f Σ_1))
        (where ((x ..._1) e_f Σ_f) (lookup l_f H_1))
        (where Σ_2 (extends ((x l) ...) Σ_1))
        (where H_2 (extends ((l v) ...) H_1))
        "E-CallK"]
   
   [--> (thread Σ_1 H_1 v (letrefk x e κ) tick)
        (thread Σ_2 H_2 e (popk Σ_1 κ)   tick)
        (where l   ,(variable-not-in (term H_1) 'l))
        (where Σ_2 (extend x l Σ_1))
        (where H_2 (extend l v H_1))
        "E-LetRefK"]
   
   [--> (thread Σ H_1 v           (setk x κ) tick)
        (thread Σ H_2 (return ()) κ          tick)
        (where l   (lookup x Σ))
        (where H_2 (extend l v H_1))
        "E-SetK"]
   
   [--> (thread Σ H v          (returnk κ) tick)
        (thread Σ H (return v) κ           tick)
        "E-ReturnK"]
   
   [--> (thread Σ_1 H_1 (return v) (bindk x e κ) tick)
        (thread Σ_2 H_2 e          (popk Σ_1 κ)  tick)
        (where l   ,(variable-not-in (term H_1) 'l))
        (where Σ_2 (extend x l Σ_1))
        (where H_2 (extend l v H_1))
        "E-BindK"]
   
   [--> (thread Σ H (return v) (seqk e κ) tick)
        (thread Σ H e          κ          tick)
        "E-SeqK"]
   
   [--> (thread Σ H v           (emitk κ) tick)
        (thread Σ H (return ()) κ         (yield v))
        "E-EmitK"]))

(define (replicate n x)
  (if (= n 0)
      null
      (cons x (replicate (- n 1) x))))

(define-metafunction Zv
  [(meta-unop - number) ,(apply - (term (number)))])

(define-metafunction Zv
  [(meta-binop =   number   number)   true]
  [(meta-binop =   number_1 number_2) false]
  [(meta-binop !=  number   number)   false]
  [(meta-binop !=  number_1 number_2) true]
  [(meta-binop <   number_1 number_2) ,(if (apply < (term (number_1 number_2))) (term true) (term false))]
  [(meta-binop +   number_1 number_2) ,(apply + (term (number_1 number_2)))]
  [(meta-binop -   number_1 number_2) ,(apply - (term (number_1 number_2)))]
  [(meta-binop *   number_1 number_2) ,(apply * (term (number_1 number_2)))]
  [(meta-binop div number_1 number_2) ,(apply quotient (term (number_1 number_2)))])

(define-metafunction Zv
  split-Σ : Σ e e -> (Σ Σ)
  [(split-Σ () e_1 e_2)
   (() ())]
  [(split-Σ ((x_1 l_1) (x_2 l_2) ...) e_1 e_2)
   (((x_1 l_1) . Σ_1) Σ_2)
   (where (Σ_1 Σ_2) (split-Σ ((x_2 l_2) ...) e_1 e_2))
   (side-condition (term (∈ x_1 (ref-vars e_1))))]
  [(split-Σ ((x_1 l_1) (x_2 l_2) ...) e_1 e_2)
   (Σ_1 ((x_1 l_1) . Σ_2))
   (where (Σ_1 Σ_2) (split-Σ ((x_2 l_2) ...) e_1 e_2))
   (side-condition (term (∈ x_1 (ref-vars e_2))))]
  [(split-Σ ((x_1 l_1) (x_2 l_2) ...) e_1 e_2)
   (((x_1 l_1) . Σ_1) ((x_1 l_1) . Σ_2))
   (where (Σ_1 Σ_2) (split-Σ ((x_2 l_2) ...) e_1 e_2))])

(define-judgment-form
  Zv
  #:mode (→z I O)
  #:contract (→z t t)
  
  [(where (t_1 ... t t_2 ...) ,(apply-reduction-relation Zred (term (thread Σ H e κ δ))))
   --------------------------------------------------------------------------------------
   (→z (thread Σ H e κ δ) t)])

(define Zmach
  (reduction-relation
   Zv
   #:domain m
   [--> (mach Φ (p_1 ... (proc (thread Σ_1 H_1 e_1 κ_1 δ_1) q_1 q_2) p_2 ...))
        (mach Φ (p_1 ... (proc (thread Σ_2 H_2 e_2 κ_2 δ_2) q_1 q_2) p_2 ...))
        (judgment-holds (→z (thread Σ_1 H_1 e_1 κ_1 δ_1) (thread Σ_2 H_2 e_2 κ_2 δ_2)))
        "P-Tick"]
   
   [--> (mach Φ_1 (p_1 ... (proc (thread Σ H e κ wait)     q_1 q_2) p_2 ...))
        (mach Φ_2 (p_1 ... (proc (thread Σ H e κ (cons v)) q_1 q_2) p_2 ...))
        (where (Φ_2 v) (dequeue Φ_1 q_1))
        "P-Consume"]
   
   [--> (mach Φ_1 (p_1 ... (proc (thread Σ H e κ (yield v)) q_1 q_2) p_2 ...))
        (mach Φ_2 (p_1 ... (proc (thread Σ H e κ tick)      q_1 q_2) p_2 ...))
        (where Φ_2 (enqueue Φ_1 q_2 v))
        "P-Yield"]
   
   [--> (mach ((q Q) ...)              (p_1 ... (proc (thread Σ H (arr e_1 e_2) κ tick) q_1 q_2) p_2 ...))
        (mach ((q_new mvar) (q Q) ...) (p_1 ... (proc (thread Σ H e_1 κ tick) q_1 q_new) (proc (thread Σ H e_2 κ tick) q_new q_2) p_2 ...))
        (fresh q_new)
        "P-Spawn"]
   
   [--> (mach ((q Q) ...)                 (p_1 ... (proc (thread Σ H (parr e_1 e_2) κ tick) q_1 q_2) p_2 ...))
        (mach ((q_new (queue)) (q Q) ...) (p_1 ... (proc (thread Σ_1 H e_1 κ tick) q_1 q_new) (proc (thread Σ_2 H e_2 κ tick) q_new q_2) p_2 ...))
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

;;
;; A simple macro to catch exceptions thrown by the error function
;;
(define-syntax try
  (syntax-rules ()
    [(_ body) (with-handlers ([exn:fail? (lambda (exn)
                                           (displayln (exn-message exn))
                                           #f)])
                body)]))