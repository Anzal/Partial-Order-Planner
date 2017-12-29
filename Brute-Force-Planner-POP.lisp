;Partial Order Planner

(defun negate (predicate)
  "Negates a predicate.  Pretty simple!"
  (cons (not (first predicate)) (rest predicate)))


(defstruct operator
   "Defines a strips operator consisting of
a NAME (a symbol or string),
a UNIQ gensym symbol assigned when the operator is added to the plan,
a list of PRECONDITIONS (predicates)
a list of EFFECTS ( predicates),

The resultant function MAKE-OPERATOR creates a *template*,
which is different from an instantiated operator actually in a plan.
Use instantiate-operator to create an operator from a template."
  name uniq preconditions effects)


;; Expect a possible warning here about redefinition
(defun copy-operator (operator)
  "Copies the operator and assigns it a new unique gensym symbol to make
it unique as far as EQUALP is concerned.  Returns the copy."
  (let ((op (copy-structure operator)))
    (setf (operator-uniq op) (gensym))
    op))



;;;;;;; LINKS
;;;;;;; A link is a structure that specifies a causal link with a from-operator,
;;;;;;; a to-operator, and precondition of the to-operator involved
;;;;;;; (which is the SAME as the effect of the from-operator!)

(defstruct (link
          (:print-function print-link))
  "FROM and TO are operators in the plan.
  PRECOND is the predicate that FROM's effect makes true in TO's precondition."
  from precond to)

(defun print-link (p stream depth)
  "Helper function to print link in a pretty way"
  (declare (ignorable depth))
  (format stream "#< (~a)~a -> (~a)~a : ~a >"
      (when (link-from p) (operator-uniq (link-from p)))
        (when (link-from p) (operator-name (link-from p)))
          (when (link-to p) (operator-uniq (link-to p)))
      (when (link-to p) (operator-name (link-to p)))
        (link-precond p)))


;;;;;;; ORDERINGS
;;;;;;; An ordering is just a dotted pair of the form (before-op . after-op)
;;;;;;; where before-op and after-op are strips operators (instances of
;;;;;;; the OPERATOR structure).  The ordering specifies
;;;;;;; that before-op must come before after-op.


(defun print-ordering (p stream depth)
  "Helper function to print link in a pretty way"
  (declare (ignorable depth))
  (format stream "#[ (~a)~a -> (~a)~a ]"
      (operator-uniq (first p))
        (operator-name (first p))
          (operator-uniq (rest p))
      (operator-name (rest p))))


;;;;;;; PLANS
;;;;;;; A plan is a list of operators, a list of orderings, and a list of
;;;;;;; links, plus the goal and start operator (which are also in the operator
;;;;;;; list).

(defstruct (plan (:print-function print-plan))
  "A collection of lists of operators, orderings, and links,
plus a pointer to the start operator and to the goal operator."
  operators orderings links start goal)

(defun print-plan (p stream depth)
  "Helper function print plan in a pretty way"
  (declare (ignorable depth))
  (format stream "#< PLAN operators: ~{~%~a~} ~%links: ~{~%~a~} ~%orderings: ~{~%~a~}~%>"
      (plan-operators p) (plan-links p)
        (mapcar #'(lambda (ordering)
              (print-ordering ordering nil 0))
            (plan-orderings p))))

;; Expect a possible warning here about redefinition
(defun copy-plan (plan)
  ;; I suggest you use this code to guarantee that the plan is copied
  ;; before you do any destructive coding on it.
  "Deep-copies the plan, and copies the operators, orderings, and links."
  (let ((p (copy-structure plan)))
    (setf (plan-operators p) (copy-tree (plan-operators p)))
    (setf (plan-orderings p) (copy-tree (plan-orderings p)))
    (setf (plan-links p) (copy-tree (plan-links p)))
    p))




;;;;;;;;; UTILITY FUNCTIONS
;;;;;;;;; I predict you will find these functions useful.

;;;; Reachable takes an association list and determines if you can reach
;;;; an item in the list from another item.  For example:
;;;;
;;;; (reachable '((a . b) (c . d) (b . c) (b . e) (e . a)) 'e 'd)
;;;; --> T   ;; e->a, a->b, b->c, c->d

(defun reachable (assoc-list from to)
  "Returns t if to is reachable from from in the association list."
  ;; expensive!

;;; You might rewrite this function to be more efficient.
;;; You could try dividing the list into two lists, one consisting of association pairs
;;; known to be reachable from FROM and ones not know to be reachable, then
;;; using the property of transitivity, move pairs from the second list to the first
;;; list, until either you discover it's reachable, or nothing else is moving.

  (dolist (x assoc-list nil)
    (when (and (equalp (car x) from)
                (or (equalp (cdr x) to)
           (reachable (remove x assoc-list) (cdr x) to)))
      (return t))))


;;;; Cyclic-assoc-list takes an association list and determines if it
;;;; contains a cycle (two objects can reach each other)
;;;;
;;;; (cyclic-assoc-list '((a . b) (c . d) (b . c) (b . e) (e . a)))
;;;; --> T   ;; a->b, b->e, e->a
;;;;
;;;; (cyclic-assoc-list '((a . a)))
;;;; --> T   ;; a->a

(defun cyclic-assoc-list (assoc-list)
  (dolist (x assoc-list nil)
    (when (reachable assoc-list (cdr x) (car x))
      (return t))))

;;;; Binary-combinations returns all N^2 combinations of T and NIL.
;;;; 
;;;; (binary-combinations 4)
;;;; -->
;;;; ((NIL T NIL T) (T T NIL T)
;;;;  (NIL NIL NIL T) (T NIL NIL T)
;;;;  (NIL T T T) (T T T T)
;;;;  (NIL NIL T T) (T NIL T T)
;;;;  (NIL T NIL NIL) (T T NIL NIL)
;;;;  (NIL NIL NIL NIL) (T NIL NIL NIL)
;;;;  (NIL T T NIL) (T T T NIL)
;;;;  (NIL NIL T NIL) (T NIL T NIL))

(defun binary-combinations (n)
  "Gives all combinations of n t's and nils"
  (let ((bag '(())))
    (dotimes (x n bag)
      (let (bag2)
  (dolist (b bag)
      (push (cons t b) bag2)
        (push (cons nil b) bag2))
  (setf bag bag2)))))



(defun before-p (operator1 operator2 plan)
  "Operator1 is ordered before operator2 in plan?"
  (if(reachable (plan-orderings plan) operator1 operator2) t nil))


(defun link-exists-for-precondition-p (precond operator plan)
  "T if there's a link for the precond for a given operator, else nil.
precond is a predicate."
  (dolist (link (plan-links plan))
    (if(and (equalp (link-to link) operator) (equalp (link-precond link) precond)) 
      (return-from link-exists-for-precondition-p t)))
nil)


(defun operator-threatens-link-p (operator link plan)
  "T if operator threatens link in plan, because it's not ordered after
or before the link, and it's got an effect which counters the link's effect."
;;; SPEED HINT.  Test the easy tests before the more costly ones.
  (if(or (equalp (link-from link) operator) (equalp (link-to link) operator)) (return-from operator-threatens-link-p nil))
  (if(reachable (plan-orderings plan) operator (link-from link)) (return-from operator-threatens-link-p nil))
  (if(reachable (plan-orderings plan) (link-to link) operator) (return-from operator-threatens-link-p nil))
  (dolist (effect (operator-effects operator))
    (if(equalp (negate effect) (link-precond link)) (return-from operator-threatens-link-p t)))
  nil)

(defun inconsistent-p (plan)
  "Plan orderings are inconsistent"
  (cyclic-assoc-list (plan-orderings plan)))


(defun open-preconds-operator(operator plan)
  "Given an Operator, returns the number of open preconditions present for it"
  (let ((count 0))
    (mapc #'(lambda(x) (if(not (link-exists-for-precondition-p x operator plan)) (incf count))) (operator-preconditions operator))
    count))

(defun pick-precond (plan)
  "Return ONE (operator . precondition) pair in the plan that has not been met yet.
If there is no such pair, return nil"
  (let* ( (op-list (mapcar #'(lambda(x) (cons x (open-preconds-operator x plan))) (plan-operators plan))) (sorted-op-list (sort op-list #'< :key #'cdr))
          (best-count 10000) (best-pair) (op-for-precond) (operator) )
    (dolist (op sorted-op-list)
      (setf operator (car op))
      (dolist (precond (operator-preconditions operator))
        (setf op-for-precond (length (all-operators precond)))
        (if(and (not (link-exists-for-precondition-p precond operator plan)) (< op-for-precond best-count))
          (progn
            (setf best-count op-for-precond)
            (setf best-pair (cons operator precond))))))
    best-pair))

(defun my-eq(a b) (if(equalp (operator-name a) (operator-name b)) t nil))

(defun all-effects(precondition plan)
  "Given a precondition, returns a list of ALL operators presently IN THE PLAN which have
effects which can achieve this precondition."
  (let ((all-ops (all-operators precondition)) (plan-ops (plan-operators plan)))
    (intersection plan-ops all-ops :test #'my-eq)))


(defun all-operators (precondition)
  "Given a precondition, returns all list of ALL operator templates which have
an effect that can achieve this
 precondition."
; Reverse because we want to get operators in the order in which they were inserted to the hash slot
; this turned out to be faster because the operators in input are ordered from lower preconditions to higher preconditions
; so we try operators with lower preconditions first
  (reverse (gethash precondition *operators-for-precond*)))

(defun is-plan-solved?(plan)
  "Returns T if plan is solved, NIL otherwise"
  (dolist (op (plan-operators plan))
    (dolist (precond (operator-preconditions op))
      (if(not (link-exists-for-precondition-p precond op plan)) (return-from is-plan-solved? nil))))
  t)

(defun select-subgoal(plan current-depth max-depth)
  "For all possible subgoals, recursively calls choose-operator
on those subgoals.  Returns a solved plan, else nil if not solved."
  (let ((op-precond-pair) (sol))
    (if(< current-depth max-depth)
      (progn
        (if(is-plan-solved? plan) (return-from select-subgoal plan))
        (setf op-precond-pair (pick-precond plan))
        (setf sol (choose-operator op-precond-pair plan (+ current-depth 1) max-depth))
        (if sol (return-from select-subgoal sol))))
    (if(is-plan-solved? plan) plan nil)))


(defun choose-operator (op-precond-pair plan current-depth max-depth)
  "For a given (operator . precondition) pair, recursively call
hook-up-operator for all possible operators in the plan.  If that
doesn't work, recursively call add operators and call hook-up-operators
on them.  Returns a solved plan, else nil if not solved."
  (let* ((operator (car op-precond-pair)) (precond (cdr op-precond-pair))
	 (new-op-added nil) (new-op nil) (plan-ops (all-effects precond plan)) (all-ops (all-operators precond)) (sol nil))
  
    (dolist (exist-op plan-ops)
      (if sol (return-from choose-operator sol))
      (setf sol (hook-up-operator exist-op operator precond plan current-depth max-depth new-op-added)))

    (dolist (current-op all-ops)
      (if sol (return-from choose-operator sol))
      (if (not (intersection (list current-op) plan-ops :test #'my-eq))
	  (progn
	    (setf new-op (copy-operator current-op))
	    (setf plan (add-operator new-op plan))
	    (setf new-op-added new-op)
	    (setf sol (hook-up-operator new-op operator precond plan current-depth max-depth new-op-added)))))
	  sol))
    

(defun add-operator (operator plan)
  "Given an OPERATOR and a PLAN makes a copy of the plan [the
operator should have already been copied out of its template at this point].
Then adds that copied operator
the copied plan, and hooks up the orderings so that the new operator is
after start and before goal.  Returns the modified copy of the plan."
 (let ((c-plan (copy-plan plan)))
  (push operator (plan-operators c-plan))
  (push (cons (plan-start c-plan) operator) (plan-orderings c-plan))
  (push (cons operator (plan-goal c-plan)) (plan-orderings c-plan))
 c-plan))

(defun hook-up-operator( from to precondition plan current-depth max-depth new-operator-was-added)
  "Hooks up an operator called FROM, adding the links and orderings to the operator
TO for the given PRECONDITION that FROM achieves for TO.  Then
recursively  calls resolve-threats to fix any problems.  Presumes that
PLAN is a copy that can be modified at will by HOOK-UP-OPERATOR. Returns a solved
plan, else nil if not solved."
  (if(before-p to from plan) (return-from hook-up-operator nil))
  (let ((c-plan (copy-plan plan)) (maybe-threatening-link) (threats))
    (setf maybe-threatening-link (make-link :from from :to to :precond precondition))
    (pushnew maybe-threatening-link (plan-links c-plan) :test #'equalp)
    (pushnew (cons from to) (plan-orderings c-plan) :test #'equalp)
    (setf threats (threats c-plan new-operator-was-added maybe-threatening-link))
    (resolve-threats c-plan threats current-depth max-depth)))


(defun threats (plan maybe-threatening-operator maybe-threatened-link)
  "After hooking up an operator, we have two places that we need to check for threats.
First, we need to see if the link we just created is threatened by some operator.
Second, IF we just added in an operator, then we need to check to see if it threatens
any links.

This function should return a list of (op . link) pairs (called ''threats'') which
indicate all the situations where some operator OP threatens a link LINK.  The only
situations you need to check are the ones described in the previous paragraph.

This function should assume that if MAYBE-THREATENING-OPERATOR is NIL, then no
operator was added and we don't have to check for its threats.  However, we must
always check for any operators which threaten MAYBE-THREATENED-LINK."
  (let ((threats nil))
    (dolist (operator (plan-operators plan))
      (if(operator-threatens-link-p operator maybe-threatened-link plan) (pushnew (cons operator maybe-threatened-link) threats :test #'equalp)))
   (if maybe-threatening-operator
    (dolist (link (plan-links plan))
      (if(operator-threatens-link-p maybe-threatening-operator link plan) (pushnew (cons maybe-threatening-operator link) threats :test #'equalp))))
    threats))

(defun all-promotion-demotion-plans (plan threats)
  "Returns plans for each combination of promotions and demotions
of the given threats, except  for the inconsistent plans.  These plans
are copies of the original plan."
  (let ((binary-combs (binary-combinations (length threats))) (all-possible-plans nil) (link) (operator) (plan-copy))
    (if(= 1 (length threats)) 
      (progn
        (setf operator (car (elt threats 0)))
        (setf link (cdr (elt threats 0)))
        (if(not (before-p operator (link-to link) plan)) (let ((c-plan (copy-plan plan))) (promote operator link c-plan) (setf all-possible-plans (append all-possible-plans (list c-plan)))))
        (if(not (before-p (link-from link) operator plan)) (let ((c-plan (copy-plan plan))) (demote operator link c-plan) (setf all-possible-plans (append all-possible-plans (list c-plan)))))
        (return-from all-promotion-demotion-plans all-possible-plans))
      (dolist (combo binary-combs)
        (setf plan-copy (copy-plan plan))
        (mapc #'(lambda(a b) (if b (promote (car a) (cdr a) plan-copy) (demote (car a) (cdr a) plan-copy))) threats combo)
        (if(not (inconsistent-p plan-copy)) (setf all-possible-plans (append all-possible-plans (list plan-copy))))))
    all-possible-plans))

(defun promote (operator link plan)
  "Promotes an operator relative to a link.  Doesn't copy the plan."
(pushnew (cons (link-to link) operator) (plan-orderings plan) :test #'equalp))  

(defun demote (operator link plan)
  "Demotes an operator relative to a link.  Doesn't copy the plan."
  (pushnew (cons operator (link-from link)) (plan-orderings plan) :test #'equalp))

(defun resolve-threats (plan threats current-depth max-depth)
  "Tries all combinations of solutions to all the threats in the plan,
then recursively calls SELECT-SUBGOAL on them until one returns a
solved plan.  Returns the solved plan, else nil if no solved plan."
  (let ((all-possible-solutions nil) (solved-plan nil))
    (if threats 
      (progn 
        (setf all-possible-solutions (all-promotion-demotion-plans plan threats))
        (dolist (solution all-possible-solutions)
          (setf solved-plan (select-subgoal solution current-depth max-depth))
          (if solved-plan (return-from resolve-threats solved-plan))))
      (setf solved-plan (select-subgoal plan current-depth max-depth)))
    solved-plan))

(defparameter *depth-increment* 1
  "The depth to increment in iterative deepening search")

(defparameter *operators-for-precond* nil
  "Hash table.  Will yield a list of operators which can achieve a given precondition")


(defun build-operators-for-precond ()
  "Buils the hash table"
  (setf *operators-for-precond* (make-hash-table :test #'equalp))
  (dolist (operator *operators*)
    (dolist (effect (operator-effects operator))
      (push operator (gethash effect *operators-for-precond*)))))

(defun do-pop ()
  (let* ((start (make-operator
      :name 'start
       :uniq (gensym)
        :preconditions nil
         :effects *start-effects*))
    (goal (make-operator
     :name 'goal
     :uniq (gensym)
     :preconditions *goal-preconditions*
     :effects nil))
     (plan (make-plan
      :operators (list start goal)
      :orderings (list (cons start goal))
      :links nil
      :start start
      :goal goal))
   (depth *depth-increment*)
	 solution)
    (setf *operators* (cons start *operators*))
    (setf *operators* (append *operators* (list goal)))
    (build-operators-for-precond)
    (loop
     (format t "~%Search Depth: ~d" depth)
     (setf solution (select-subgoal plan 0 depth))
     (when solution (return)) ;; break from loop, we're done!
     (incf depth *depth-increment*))
    (format t "~%Solution Discovered:~%~%")
    solution))

#|

(defparameter *operators*
  (list
   ;; move from table operators
   (make-operator :name 'a-table-to-b
       :preconditions '((t a-on-table) (t b-clear) (t a-clear))
        :effects '((nil a-on-table) (nil b-clear) (t a-on-b)))
   (make-operator :name 'b-table-to-a
       :preconditions '((t b-on-table) (t a-clear) (t b-clear))
        :effects '((nil b-on-table) (nil a-clear) (t b-on-a)))
   ;; move to table operators
   (make-operator :name 'a-b-to-table
       :preconditions '((t a-on-b) (t a-clear))
        :effects '((t a-on-table) (nil a-on-b) (t b-clear)))
   (make-operator :name 'b-a-to-table
       :preconditions '((t b-on-a) (t b-clear))
        :effects '((t b-on-table) (nil b-on-a) (t a-clear))))
  "A list of strips operators without their uniq gensyms set yet -- 
doesn't matter really -- but NOT including a goal or start operator")


;;; b is on top of a
(defparameter *start-effects*
  '((t a-on-table) (t b-on-a) (t b-clear)))

;;; a is on top of b
(defparameter *goal-preconditions*
  ;; somewhat redundant, is doable with just ((t a-on-b))
  '((t a-on-b) (t b-on-table) (t a-clear)))

|#

;;;;;; THREE-BLOCK-WORLD
;;;;;; you have three blocks on the table, A, B, and C.
;;;;;;
;;;;;;
;;;
;;; Why so many operators?  Because we don't have a variable facility.
;;; We can't say MOVE(x,y,z) -- we can only say MOVE(A,TABLE,B).  To
;;; add in a variable facility is a lot more coding, and I figured I'd
;;; save you the hassle of unification.  If you want to give it a shot,
;;; I have written up some unification code which might help you out.
;;; Another consequence of not having a variable facility is that you
;;; can't rely on the least-commitment heuristic of not immediately
;;; binding variables to constants.  For us, we must *immediately*
;;; commit to constants.  That makes our search space much nastier.
;;; C'est la vie!
;;;
 (defparameter *operators*
   (list
    ;; move from table operators
    (make-operator :name 'a-table-to-b
   :preconditions '((t a-on-table) (t b-clear) (t a-clear))
   :effects '((nil a-on-table) (nil b-clear) (t a-on-b)))
    (make-operator :name 'a-table-to-c
   :preconditions '((t a-on-table) (t c-clear) (t a-clear))
   :effects '((nil a-on-table) (nil c-clear) (t a-on-c)))
    (make-operator :name 'b-table-to-a
   :preconditions '((t b-on-table) (t a-clear) (t b-clear))
   :effects '((nil b-on-table) (nil a-clear) (t b-on-a)))
    (make-operator :name 'b-table-to-c
   :preconditions '((t b-on-table) (t c-clear) (t b-clear))
   :effects '((nil b-on-table) (nil c-clear) (t b-on-c)))
    (make-operator :name 'c-table-to-a
   :preconditions '((t c-on-table) (t a-clear) (t c-clear))
   :effects '((nil c-on-table) (nil a-clear) (t c-on-a)))
    (make-operator :name 'c-table-to-b
   :preconditions '((t c-on-table) (t b-clear) (t c-clear))
   :effects '((nil c-on-table) (nil b-clear) (t c-on-b)))
    ;; move to table operators
    (make-operator :name 'a-b-to-table
   :preconditions '((t a-on-b) (t a-clear))
   :effects '((t a-on-table) (nil a-on-b) (t b-clear)))
    (make-operator :name 'a-c-to-table
   :preconditions '((t a-on-c) (t a-clear))
   :effects '((t a-on-table) (nil a-on-c) (t c-clear)))
    (make-operator :name 'b-a-to-table
   :preconditions '((t b-on-a) (t b-clear))
   :effects '((t b-on-table) (nil b-on-a) (t a-clear)))
    (make-operator :name 'b-c-to-table
   :preconditions '((t b-on-c) (t b-clear))
   :effects '((t b-on-table) (nil b-on-c) (t c-clear)))
    (make-operator :name 'c-a-to-table
   :preconditions '((t c-on-a) (t c-clear))
   :effects '((t c-on-table) (nil c-on-a) (t a-clear)))
    (make-operator :name 'c-b-to-table
   :preconditions '((t c-on-b) (t c-clear))
   :effects '((t c-on-table) (nil c-on-b) (t b-clear)))
    ;; block-to-block operators
    (make-operator :name 'a-b-to-c
   :preconditions '((t a-on-b) (t a-clear) (t c-clear))
   :effects '((nil a-on-b) (t a-on-c) (nil c-clear) (t b-clear)))
    (make-operator :name 'a-c-to-b
   :preconditions '((t a-on-c) (t a-clear) (t b-clear))
   :effects '((nil a-on-c) (t a-on-b) (nil b-clear) (t c-clear)))
    (make-operator :name 'b-a-to-c
   :preconditions '((t b-on-a) (t b-clear) (t c-clear))
   :effects '((nil b-on-a) (t b-on-c) (nil c-clear) (t a-clear)))
    (make-operator :name 'b-c-to-a
   :preconditions '((t b-on-c) (t b-clear) (t a-clear))
   :effects '((nil b-on-c) (t b-on-a) (nil a-clear) (t c-clear)))
    (make-operator :name 'c-a-to-b
   :preconditions '((t c-on-a) (t c-clear) (t b-clear))
   :effects '((nil c-on-a) (t c-on-b) (nil b-clear) (t a-clear)))
    (make-operator :name 'c-b-to-a
   :preconditions '((t c-on-b) (t c-clear) (t a-clear))
   :effects '((nil c-on-b) (t c-on-a) (nil a-clear) (t b-clear))))

   "A list of strips operators without their uniq gensyms set yet -- 
 doesn't matter really -- but NOT including a goal or start operator")

 (defparameter *start-effects*
;;   ;; Sussman Anomaly
   '((t a-on-table) (t b-on-table) (t c-on-a) (t b-clear) (t c-clear))
   "A list of predicates which specify the initial state")


#|
 (defparameter *start-effects*
   ;; another simple situation: all on table
   '((t a-on-table) (t a-clear)
    (t b-on-table) (t b-clear)
     (t c-on-table) (t c-clear))) 


(defparameter *start-effects*
  ;;For the difficult problem we tried which is not so difficult
  '((t c-on-b) (t b-on-a) (t a-on-table) (t c-clear)))

|#

 (defparameter *goal-preconditions*
'((t a-on-b) (t b-on-c) (t c-on-table) (t a-clear)))
