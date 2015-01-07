
;;;;;;;;;;;;;;;;;;; Unification ;;;;;;;;;;;;;;;;;;;;;;;;
;; Based off of code provided in class lectures

(defstruct (compound (:conc-name nil)) op args)

(defun var-p (x)
  (and (symbolp x) (eql (elt (symbol-name x) 0) #\=)))

(defun unify (x y &optional (theta nil))
       (cond
	 ((eql theta 'fail) 'fail)
	 ((eql x y) theta)
	 ((var-p x) (unify-var x y theta))
	 ((var-p y) (unify-var y x theta))
	 ((and (compound-p x) (compound-p y)) (unify (args x) (args y) (unify (op x) (op y) theta)))
	 ((and (listp x) (listp y)) (unify (cdr x) (cdr y) (unify (car x) (car y) theta)))
	 (t 'fail)
	))

(defun unify-var (var x theta)
  (let ((varbinding (assoc var theta))
	(xbinding (assoc x theta))
	(xsub (substitute-term theta x)))
    (cond 
      (varbinding (unify (cdr varbinding) x theta))
      (xbinding (unify var (cdr xbinding) theta))
      ((occurs-p var xsub) 'fail)
      (t (cons (cons var xsub) theta))
    )))

(defun occurs-p (var sub)
  (cond
    ((null sub) nil)
    ((eql var sub) 't)
    ((compound-p sub) (or (occurs-p var (op sub)) (occurs-p var (args sub))))
    ((listp sub) (or (occurs-p var (car sub)) (occurs-p var (cdr sub))))
    (t nil)
  ))

;;;;;;;;;;;;;;;;;;;;; Substitution ;;;;;;;;;;;;;;;;;;;;;;;;
;; Substitutions are done on copies. This is necessary in 
;; order to reuse resolvent
(defun substitute-term (theta body)
  (cond
    ((null theta) body)
    (t (substitute-term (cdr theta) (substitute-binding (car theta) body)))
  ))

(defun substitute-binding (binding body)
  (cond
    ((null body) nil)
    ((symbolp body) (if (equal body (car binding)) 
		     (cdr binding) 
		     body))
    ((compound-p body)  (let ((copy-body (copy-compound body)))
			      (when (member (car binding) (args copy-body))
				  (setf (args copy-body) (substitute-binding binding (args copy-body)))) 
			      copy-body))
    (t (cons (substitute-binding binding (car body)) (substitute-binding binding (cdr body))))
  ))

;;;;;;;;;;;;;;;;;;;;;;;;;; Automated Theorem Prover ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; I use the set of support heuristic by initializing it to nq. All resolutions
;; include at least one member for the set of support, while the other sentences (kb)
;; are jointly satisfiable (p. 355), making it complete.
;;
;; Representation:
;; An SNF sentence is a conjuction of disjunctions. I refer to each conjunction term
;; as simply a clause. Since this is a strict requirement, there is no need to 
;; represent logical connectives (AND and OR) in the input SNF sentence
;; The SNF sentence, for example, a knowledge base, is represented as:
;; (list clause1 clause2 ...). Being in a list implies that they are being ANDed 
;; together. The list is REQUIRED even if there is only clause
;; 
;; A clause is series of disjunctions. I refer to each disjunction term as simply a term.
;; A clause is represented as:
;; (list term1 term2 ...). Being in a list implies that they are being ORed together.
;; As with above, this list is REQUIRED even if there is only clause
;;
;; A term is any literal or compound or the negatation of each. Now, as above, I could
;; have simply represented negation by adding another nested list, I choose to, for
;; readability to simply represented a negated term as (list 'not term), where term is
;; is a literal or a compound.
;;
;; The negated query is a clause (i.e. a series of disjunctions) and must be
;; provided as such
;;
;; Variables are represented by prefixing them with '='. Example: variable x is =x
;; Constants are simply atoms (do not prefix them with = however)
;; Predicates and functions (skolem) are represented as compounds. Example: Knows(x,y)
;; is represented as (make-compound :op 'Knows :args '(=x =y))
;; Knows(Mother(x), John) is represented as:
;; (make-compound :op 'Knows :args (list (make-compound :op 'Mother :args '(=x)) 'John))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; **************************************IMPORTANT ASSUMPTION************************************************
;; I assumed that the triples that were to be returned were ALL the resolvents generated while looking for 
;; the nil resolvent. I was not sure if the triples to be returned were to be the PROOF (i.e. all resolvents
;; that directly generate the nil resolvent in a sequence). I contacted Ms. Sarah Alkuhlani and she said 
;; either way is fine as the specification was not clear. Since the heuristic is good, the returned triples
;; do not contain a lot of useless resolutions. For instance, one proof consists of nine resolutions while
;; my theorem prover returns twenty five.

(defvar *triples* nil)

(defun atp (kb nq)
  (progn 
    (setf *triples* nil)
    (cond
      ((null kb) 'nil)
      ((null nq) 'No-Query-Vacuously-True)
      (t (let* ((set-of-support (list nq))
		(result (resolve-all kb set-of-support)))
	   (unless (null result)
	     *triples*)))
  )))

;; For efficiency, I try resolutions that include one clause from the set of support
;; and one from the kb first before moving to clauses only within the set of support, as
;; most proofs rely on axioms in the kb.
;; Since clauses are never lost, resolution fails when no new clauses
;; are created. That is, no resolvent is produced using the set of support and the kb
;; followed immediately by no resolvent produced amongst clauses in the set of support.
;; If lisp had some continuation mechanism, it would be much cleaner to simply return
;; failures or successes. Instead, I have to check everytime and tail recurse.
;; Note, that I do a sort of "depth-first" resolution of clauses. I take the first
;; clause from the set of support and add all resolutions from it back to the FRONT of
;; set of  support (after reversing them to maintain the order). Then, I tail recurse
;; repeating the process. Only when no resolvents are produced do I move on to the the
;; second, third and so on members of the set of support. Finally, if none of them
;; produce any resolvents, I try clauses within the set of support and if that also
;; fails, I return nil.
;; I have indented this carefully, so that it is readable in any window where the 
;; size is greater than 130.
(defun resolve-all (kb sos)
  (cond
     ((null sos) nil)
     (t (let ((new-kb-resolvents (resolve-one kb (car sos))))
	  (cond
	    ((eq new-kb-resolvents 't) 't)
	    ((null new-kb-resolvents) (let ((rest (resolve-all kb (cdr sos))))
					(cond
					  ((null rest) (let ((new-sos-resolvents (resolve-one sos (car sos))))
							 (cond
							   ((eq new-sos-resolvents 't) 't)
							   ((null new-sos-resolvents) (let ((rest (resolve-all sos (cdr sos))))
											(cond
											  ((null rest) nil)
											  ((eq rest 't) 't)
											  (t (resolve-all kb (append rest sos)))
											)))
							   (t (resolve-all kb (append (reverse new-sos-resolvents) sos)))
							 )))
					  ((eq rest 't) 't)
					  (t (resolve-all kb (append rest sos)))
					)))
	    (t (resolve-all kb (append (reverse new-kb-resolvents) sos)))
	  )))
    ))

;; I use the return-from special form to return immediately when a nil resolvent
;; is found.
(defun resolve-one (kb clause)
  (let ((resolvents nil))
    (do ((ckb kb (cdr ckb)))
	((null ckb) resolvents)
      (let ((result (find-unifiers (car ckb) clause)))
	(cond
	  ((null result) (return-from resolve-one 't))
	  ((eq result 'fail) nil)
	  (t (setf resolvents (append result resolvents)))
	))
    )))

;; Iterates through both clauses, trying to unify
;; Produces all resolvents for a particular clause clause pairing
;; Adds them to the list of triples and constructs our resolvents list
;; Finally after all possible unifications are done, checks to see if
;; we have nil somewhere in our resolvent(s) list
(defun find-unifiers (clause1 clause2)
  (let ((resolvents 'fail))
    (do ((c1 clause1 (cdr c1)))
	((null c1) resolvents)
      (do ((c2 clause2 (cdr c2)))
	  ((null c2) nil)
	(when (complementaryp (car c1) (car c2))
	  (let* ((term1 (remove-negative (car c1)))
		 (term2 (remove-negative (car c2)))
		 (result (unify term1 term2)))
	    (cond
	      ((eq result 'fail) nil)
	      (t (let ((resolvent (construct-resolvent clause1 clause2 (car c1) (car c2) result)))
		   (setf *triples* (cons (list clause1 clause2 resolvent) *triples*))
		   (setf resolvents (if (eq resolvents 'fail)
					    (cons resolvent nil)
					    (cons resolvent resolvents)))
		 ))
	    )))
      ))
    (cond 
      ((provedp resolvents) nil)
      (t resolvents)
    )))
 
(defun complementaryp (term1 term2)
  (or (and (listp term1) (not (listp term2))) (and (listp term2) (not (listp term1)))) )

(defun remove-negative (term)
  (if (listp term)
      (cadr term)
      term))

;; Given a theta, the two clauses and the two terms that unified,
;; constructs the resolvent appropriately and also removes duplicates
;; as it possible to have a resolvent with two clauses that are the same
;; Since it is in SNF and the two duplicate clauses are or'ed together
;; it is fine to remove them.
(defun construct-resolvent (clause1 clause2 term1 term2 theta)
  (let ((resolvent nil))
    (do ((c1 clause1 (cdr c1)))
	((null c1) nil)
      (unless (equalp (car c1) term1)
	(if (eq theta 't)
	    (setf resolvent (cons (car c1) resolvent))
	    (setf resolvent (cons (substitute-term theta (car c1)) resolvent))
	)))
    (do ((c2 clause2 (cdr c2)))
	((null c2) nil)
      (unless (equalp (car c2) term2)
	(if (eq theta 't)
	    (setf resolvent (cons (car c2) resolvent))
	    (setf resolvent (cons (substitute-term theta (car c2)) resolvent))
	)))
    (remove-duplicates resolvent :test #'equalp)))

(defun provedp (resolvent)
  (if (or (null resolvent) (eq resolvent 'fail)) 
      nil
      (or (null (car resolvent)) (provedp (cdr resolvent)))
  ))

(defun record-triples (clause1 clause2 resolvents)
  (cond
    ((null resolvents) nil)
    (t (progn (setf *triples* (cons (list clause1 clause2 (car resolvent)) *triples*))
	      (record-triples clause1 clause2 (cdr resolvents))))
  ))
