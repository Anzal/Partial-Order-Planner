# Partial-Order-Planner

 SIMPLE-PLAN
;;;;;;;; The following planner is a brute-force planning partial-order (POP) system.  
;;;;;;;; It doesn't use a heuristic, but instead just uses iterative-deepening search.  
;;;;;;;; If you want to see a high-quality, free POP planner, check out UCPOP at
;;;;;;;; https://www.cs.washington.edu/ai/ucpop.html
;;;;;;;; Note that there are many better planners still at this point (POP is getting old).
;;;;;;;;
;;;;;;;; The following planner does not use variables -- it's propositional and not
;;;;;;;; predicate-logic based.  Because it doesn't use
;;;;;;;; variables, we have to write more code to describe a problem (see the Blocks World
;;;;;;;; example at end) but it is a much easier algorithm to for you to write (you don't have to
;;;;;;;; be involved in unification.)


Set your Operators,  
Set your Start Effects, 
Set your Goal Preconditions, 
Run the (do-pop) function and it will give you the solved plan with all the links and orderings.
