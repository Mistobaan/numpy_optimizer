; node class
(defclass node (is-a USER)
	  (role concrete)
	  (pattern-match reactive)
	  (slot id (type INTEGER) (create-accessor read-write))
	  (slot eq-class (type SYMBOL) (create-accessor read-write))
	  (slot type (type SYMBOL))
	  (multislot args)
	  (multislot children (type SYMBOL) (create-accessor read-write) (default (create$ )))
	  (multislot loop-variance-indices (type INTEGER) (default (create$ -1)))
	  (slot loop-depth (type INTEGER) (default -1))
	  (slot expr-type (type SYMBOL) (default unknown))
	  (multislot shape (type INTEGER) (default (create$ -1)))
)

; current-id counter
(deftemplate current-id (slot value (type INTEGER)))

; class equality info
(deftemplate equal-classes (slot fst (type SYMBOL)) (slot snd (type SYMBOL)))

(deffunction get-current-id ()
	     (fact-slot-value (nth$ 1 (find-fact ((?ci current-id)) TRUE)) value))

; only for negative class ids
(deffunction find-class-id (?class-name)
	     (+ (str-index "class-" (str-cat ?class-name)) 5))

(deffunction is-negative-id (?class-name)
                    (neq (str-index "class-" (str-cat ?class-name)) FALSE))

(deffunction transform-class-id (?class-name)
                    (if (is-negative-id ?class-name) then
		    	        (return (string-to-field (str-cat "class" (str-cat
                        	(- (string-to-field
                            	    (sub-string (find-class-id ?class-name) (str-length ?class-name) ?class-name))
	                       	    (get-current-id)
	                        )
                    )))))
                    (return ?class-name)
)

(deffunction transform-all-chld-ids ($?children)
                    (if (= (length $?children) 0)
                        then (return $?children)
                    )
                    (return (insert$ (transform-all-chld-ids (rest$ $?children)) 1
                                (transform-class-id (nth$ 1 $?children))))
)

(deffunction transform-id (?id)
	     		(if (< ?id 0) then
			    (return (- ?id (get-current-id))))
			(return ?id))

(deffunction replace-eq-class (?class-name ?lhs-class ?rhs-class)
	     		(if (eq ?class-name ?rhs-class) then
                            (return ?lhs-class))
                        (return ?class-name)
)

(deffunction replace-children (?lhs-class ?rhs-class $?children)
                        (if (= (length$ $?children) 0)
                            then (return $?children)
                        )
                        (return (insert$ (replace-children ?lhs-class ?rhs-class (rest$ $?children)) 1
                                    (replace-eq-class (nth$ 1 $?children) ?lhs-class ?rhs-class)))
)



(deffunction check-leaf-class-absence (?class-id)
                        (= (length$
                                (find-all-instances ((?n node)) (eq ?n:eq-class ?class-id))
                            )
                            0)
)

(defrule apply-equality
                    ?e <- (equal-classes (fst ?lhs-class) (snd ?rhs-class))
                    (test (neq ?lhs-class ?rhs-class))
                    =>
                    (do-for-all-instances ((?n node)) TRUE
                        (bind ?eq-cl (replace-eq-class (send ?n get-eq-class) ?lhs-class ?rhs-class))
                        (bind ?chldrn (replace-children ?lhs-class ?rhs-class (send ?n get-children)))
                        (modify-instance ?n
                            (eq-class ?eq-cl)
                            (children ?chldrn)
                        )
                        ;(send ?n print)
                        ;(printout t "-------------" crlf)
                    )
)

(deffunction all (?arr)
                 (if (= (length$ ?arr) 0) then (return TRUE))
                 (progn$ (?elem ?arr) (if (eq ?elem FALSE) then (return FALSE)))
                 (return TRUE))



(deffunction same (?type1 ?args1 ?chldrn1 ?n2)
    (bind ?type2 (send ?n2 get-type))
    (if (eq ?type1 "THETANode")
        then (return FALSE)
    )
    (if (eq ?type2 "THETANode")
        then (return FALSE)
    )
    (if (neq ?type1 ?type2)
        then (return FALSE)
    )
    (bind ?chldrn2 (send ?n2 get-children))
    (if (neq ?chldrn1 ?chldrn2)
        then (return FALSE)
    )
    (bind ?args2 (send ?n2 get-args))
    (if (neq ?args1 ?args2)
        then (return FALSE)
    )
    (return TRUE)
)

(deffunction already-exists (?type ?args ?chldrn)
    (bind ?instances (find-instance ((?n2 node)) (same ?type ?args ?chldrn ?n2)))
    (if (= (length$ ?instances) 0)
        then (return FALSE)
    )
    (bind ?n2 (nth$ 1 ?instances))
    (return (send ?n2 get-eq-class))
)

(defglobal ?*created-instances-counter* = 0)