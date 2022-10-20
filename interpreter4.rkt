; If you are using scheme instead of racket, comment these two lines, uncomment the (load "simpleParser.scm") and comment the (require "simpleParser.rkt")
#lang racket
;(require "functionParser.rkt")
; (load "simpleParser.scm")
(require "classParser.rkt")

;;;*****************************************************************
;;; Reed Bower(rlb182) Haocheng He(hxh461) Walter Graham(wxg136)
;;; CSDS345
;;;*****************************************************************

; *** PART 4 NOTES ****
; Comments that start with *** are pertinent to this part of the assignment, and indicate new or updated functions
; Below are some explanations for the points labeled in the assignment rubric (others are indicated where it was implemented)
; Point 4: compile-type was added to all interpret and eval functions
; Point 9: included in mvalue and interpret function (had some issues with lookup for methods, but the mvalue return works)
; Point 10: could not implement



; TO RUN THIS PROGRAM, mimic the following command (interpret "filename.txt") --> assuming the txt file is within the same directory
; NEEDS to be in the same directory as lex.rkt and simpleParser.rkt to work




; An interpreter for the simple language using tail recursion for the M_state functions and does not handle side effects.

; The functions that start interpret-...  all return the current environment.  These are the M_state functions.
; The functions that start eval-...  all return a value.  These are the M_value and M_boolean functions.

; The main function.  Calls parser to get the parse tree and interprets it with a new environment.  Sets default continuations for return, break, continue, throw, and "next statement"


; *** Changed this method to include not only the file name, but the class that is desired to have their main method executed
(define interpret
  (lambda (file class)
    (scheme->language
     (interpret-global-classes (parser file) (newenvironment) (lambda (v s) v s)
                               (lambda (env) (myerror "Break used outside of loop")) (lambda (env) (myerror "Continue used outside of loop"))
                               (lambda (v env) (myerror "Uncaught exception thrown")) (lambda (env) env) class))))


; Helper method to print out the parestree
(define testI
  (lambda (filename)
    (parser filename)))


; *** Point 1: top level that only handles global statements, which are class definitions

; *** Interprets outer or global statements
(define interpret-global-classes
  (lambda (statement-list environment return break continue throw next class)
    (if (null? statement-list)
        (interpret-statement-list(get-closure-body(get-main-closure(get-closure-methods(lookup class environment)))) environment return break continue throw next class) 
        (interpret-global-statement (car statement-list) environment return break continue throw (lambda (env) (interpret-global-classes (cdr statement-list) env return break continue throw next class))))))
  
; *** Interprets individual global statement which is either a class definition of invalid
(define interpret-global-statement
  (lambda (statement environment return break continue throw next)
    (cond
      ((eq? 'class (statement-type statement)) (interpret-class statement environment throw next))
      (else (myerror "Invalid global statement: " (statement-type statement)))
      )))

; *** Helper method to find the closure of the main method from within the class closure
(define get-main-closure
  (lambda (methods)
      (class-main-closure (get-closure-method-names methods) (get-closure-method-closures methods))
    ))

; *** Searches for function 'main
(define class-main-closure
  (lambda (method-names method-closures)
    (cond
      ((null? method-names) (myerror "No main method in class"))
      ((and (eq? (car method-names) 'main) (eq? (cdr method-closures) (cdr method-closures))) (car method-closures))
      ((class-main-closure(cdr method-names) (cdr method-closures)))
      )))

; *** Interprets the class, inserting the class closure into the environment
(define interpret-class
  (lambda (statement environment throw next)
       (next (insert (class-name statement) (create-class-closure (super-class statement) (interpret-outer-statement-list (class-body statement) (newenvironment) throw (lambda (env) env) (class-name statement)) environment) environment)) ; (function-parameters statement) (function-body statement)  (topframe environment) (function-name statement)) environment))
    ))

  
; interprets a list of statements.  The state/environment from each statement is used for the next ones.
(define interpret-statement-list
  (lambda (statement-list environment return break continue throw next current-type)
    (if (null? statement-list)
        (next environment)
        (interpret-statement (car statement-list) environment return break continue throw (lambda (env) (interpret-statement-list (cdr statement-list) env return break continue throw next current-type)) current-type))))

; *** CHANGED TO RETURN THE CLOSURE OF THE FUNCTION
; *** Point 2: middle level only interpets function and variable declarations
; similar to interpret-statement-list but does it on the outer calls (ie global variables and functions)
(define interpret-outer-statement-list
  (lambda (statement-list environment throw next current-type)
    (if (null? statement-list)
        (next environment)
        (interpret-outer-statement (car statement-list) environment throw (lambda (env) (interpret-outer-statement-list (cdr statement-list) env  throw next current-type)) current-type))))

; parses for declare assign and function types only
(define interpret-outer-statement
  (lambda (statement environment throw next current-type)
    (cond
      ((eq? 'var (statement-type statement)) (interpret-declare statement environment next throw current-type))
      ((eq? '= (statement-type statement)) (interpret-assign statement environment next current-type))
      ((eq? 'function (statement-type statement)) (interpret-function statement environment next current-type))
      ((eq? 'static-function (statement-type statement)) (interpret-function statement environment next current-type))
      (else (myerror "Invalid outer statement: " (statement-type statement))))))

; creation of closure and binding it to the name within the environment
(define interpret-function
  (lambda (statement environment next current-type)
    (next (insert (function-name statement) (create-closure (function-parameters statement) (function-body statement)  (topframe environment) (function-name statement) current-type) environment))))




; *** Point 3: Class closure created with required components
; *** creation of class closure --> need to include super class, methods, static fields, instance field names
; *** didn't end up reaching the polymorphism part of the assignment, but had set up the closure creation to handle that down the line
(define create-class-closure
  (lambda (super-class bindings environment)
    (cond
      ((null? super-class) (cons super-class (cons (methods-list(binding-names bindings) (binding-values bindings) (newframe))
                                             (cons (instance-fields-list (binding-names bindings) (binding-values bindings) '())
                                             (cons (instance-values-list (binding-names bindings) (binding-values bindings) '())
                                             (cons (class-var-index(instance-values-list (binding-names bindings) (binding-values bindings) '()) 0) '()))))))
      ; appending the values from the super-class as described in the lecture
      ((cons super-class (cons (cons (methods-list(binding-names bindings) (binding-values bindings) (newframe)) (get-super-methods super-class environment))
                                             (cons (cons (instance-fields-list (binding-names bindings) (binding-values bindings) '()) (get-super-instance-names super-class environment))
                                             (cons (cons (get-super-instance-names super-class environment) (instance-values-list (binding-names bindings) (binding-values bindings) '()))
                                             (cons (+ (get-super-index super-class environment) ((class-var-index(instance-values-list (binding-names bindings) (binding-values bindings) '()) 0))) '())  )))))
      )))


; *** HELPER METHODS FOR RETRIEVING SUPER CLASS CLOSURE LISTS ***

; *** gets the methods from the super class if there is one
(define get-super-methods
  (lambda (super-class environment)
    (get-closure-methods(lookup super-class environment))
    ))

; *** gets the instance names from super class if there is one
(define get-super-instance-names
  (lambda (super-class environment)
    (get-closure-instance-names(lookup super-class environment))
    ))
; *** gets the instance values from super class
(define get-super-instance-values
  (lambda (super-class environment)
    (get-closure-instance-values(lookup super-class environment))
    ))

; *** gets the index associated to the suepr class's pointer in the variable list (as described in lecture)
(define get-super-index
  (lambda (super-class environment)
    (get-closure-index(lookup super-class environment))
    ))


; *** HELPER METHODS FOR CLASS CLOSURE ***

; *** gets the index of the last var in the class
(define class-var-index
  (lambda (var-list index)
    (cond
      ((null? var-list) index)
      (class-var-index (cdr var-list) (+ 1  index)))))

; *** gets the list of methods and their closures
(define methods-list
  (lambda (names values frame)
    (cond
      ((null? names) frame)
      ((list? (car values)) (methods-list (cdr names) (cdr values) (add-to-frame (car names) (car values) frame)))
      ((methods-list(cdr names)(cdr values) frame))
        
    )))

; *** creates the list of instance fields
(define instance-fields-list
  (lambda (names values list)
    (cond
      ((null? names) list)
      ((not (list? (car values)))(instance-fields-list (cdr names) (cdr values) (cons (car names) list)))
      ((instance-fields-list(cdr names) (cdr values) list))
      )))

; *** creates the instance values from class closure
(define instance-values-list
  (lambda (names values list)
    (cond
      ((null? names) (reverse-list list))
      ((not (list? (car values))) (instance-values-list (cdr names) (cdr values) (cons (car values) list)))
      ((instance-values-list(cdr names) (cdr values) list))
      )))

; *** Reverses the list - to follow what was shown in lecture
(define reverse-list
  (lambda (lis)
  (if (null? lis)
     lis
     (append (reverse-list (cdr lis)) (list (car lis)))
  )
))

; *** list of values given the bindings
(define binding-values
  (lambda (bindings)
    (cadar bindings)
    ))

; *** list of the var names given the bindings
(define binding-names
  (lambda (bindings)
    (caar bindings)
    ))

; *** gets the class name given the statement
(define class-name
  (lambda (statement)
    (cadr statement)))

; *** gets the super-class given the statement
(define super-class
  (lambda (statement)
    (cond
      ((null? (caddr statement)) '())
      ((super-class-name (caddr statement)))
       )))

; *** gets the name of the super class
(define super-class-name
  (lambda (super-class-statement)
    (cadr super-class-statement)
    ))

; *** the body of the class given teh 
(define class-body
  (lambda (statement)
     (cadddr statement)))

; *** gets the super-class value from the closure
(define get-closure-super-class
  (lambda(closure)
    (car closure)))

; *** gets the instance names from the closure
(define get-closure-instance-names
  (lambda (closure)
    (caddr closure)))

; *** gets the instance values from the closure
(define get-closure-instance-values
  (lambda (closure)
    (cadddr closure)))

; *** gets the methods list from the closure
(define get-closure-methods
  (lambda (closure)
    (cadr closure)
    ))

; *** gets the method names given the list of methods
(define get-closure-method-names
  (lambda (methods)
    (car methods)))

; *** gets the method closures given the list of methods
(define get-closure-method-closures
  (lambda (methods)
    (cadr methods)))

; *** gets the index from the closure
(define get-closure-index
  (lambda (closure)
    (cadr(cdddr closure))))

; *** INSTANCE CLOSURE CREATED AND HELPER METHODS ***
; *** Point 5: instance closure created
; *** Creates the instance closure that consists of the class and a copy of the instance values
(define create-instance-closure
  (lambda (class environment)
    (cons class (cons (get-closure-instance-values(lookup class environment)) '()))
    ))

; *** get instance values from instance closure 
(define get-instance-closure-values
  (lambda (closure)
    (cadr closure)))

; *** get the class of the instance closure
(define get-instance-closure-class
  (lambda (closure)
    (car closure)))



; *** adding 'this to the list of params in the function closures
(define add-this-to-params
  (lambda (parameters)
    (cond
      ((null? parameters) (list 'this) )
      ((cons (car parameters) (add-this-to-params (cdr parameters))))
      )))


; *** Point 6: inclusion of current type when creating new function closure
; creates the closure with the parameters, body of function and scope
(define create-closure
  (lambda (parameters body environment name current-type)
    (cons  (add-this-to-params parameters ) (cons body (cons (cons name (variables environment)) (list current-type ))))
    ))

; *** gets the current type from function closure
(define get-closure-current-type
  (lambda (closure)
    (cadddr closure)))

; returns the closure variable names within scope
(define get-closure-variables-scope
  (lambda (closure)
    (caddr closure)))

; inserts the closure
(define insert-closure-state
  (lambda (var value frame)
    (insert var value frame)))

; returns the closure's state
(define get-closure-state
  (lambda (closure environment)
    (cond
      ((null? (get-closure-variables-scope closure)) '())
      (else (create-closure-state (get-closure-variables-scope closure)  environment (newenvironment) ))
      )))

; creates the closure's state, with the values to match the variables 
(define create-closure-state
  (lambda (vars environment state)
    (cond
      ((null? vars) state)
      (else (create-closure-state(cdr vars) environment (insert (car vars) (lookup (car vars) environment) state)))
      )))
                                       
; returns the closure's parameters
(define get-closure-parameters
  (lambda (closure)
    (car closure)))

; returns the closure's body which is the functions statement-list
(define get-closure-body
  (lambda (closure)
    (cadr closure)))

; binds the actual-parameters to the formal-parameters
(define bind-parameters
  (lambda (formal-parameters actual-parameters environment function-state throw next)
    (cond
      ((not (= (length formal-parameters) (length actual-parameters))) (myerror "error: Mismatched parameters and arguments"))
      ((and (null? actual-parameters)  (null? formal-parameters)) function-state)
      ((null? (cdr formal-parameters)) (insert (car formal-parameters) (eval-expression (car actual-parameters) environment throw next ) function-state))
      (else (bind-parameters (cdr formal-parameters) (cdr actual-parameters) environment  (insert (car formal-parameters) (eval-expression (car actual-parameters) environment throw next) function-state) throw next)) ; INCLUDE throw
      )))



; evaluates the function when used as an expression using the closure given the name
(define eval-function-expression
  (lambda (name actual-parameters environment throw next current-type)
    
   (interpret-statement-list
     (get-closure-body(get-func-closure(get-closure-methods(lookup current-type environment)) name))
     (push-frame(function-state-2 name actual-parameters environment (function-state-1 name environment) throw next) )
     (lambda (s v)  (update-state environment s) v)
     (lambda (s) (myerror "break outside of loop"))
     (lambda (s) (myerror "continue outside of loop"))
     throw
     (lambda (s) (next s))
    )
    ) )

; *** returns the function's closure from within the class's closure
(define get-func-closure
  (lambda (methods name)
      (class-func-closure (get-closure-method-names methods) (get-closure-method-closures methods) name)
    ))

; *** searches for the desired function from within the method names
(define class-func-closure
  (lambda (method-names method-closures name)
    (cond
      ((null? method-names) (myerror "No method in class"))
      ((and (eq? (car method-names) name) (eq? (cdr method-closures) (cdr method-closures))) (car method-closures))
      ((class-func-closure(cdr method-names) (cdr method-closures)))
      )))


; function-state-1 as described in lecture
(define function-state-1
  (lambda (name environment)
    (cond
      ((null? (get-closure-state (lookup name environment) environment)) (newenvironment))
      (else (get-closure-state (lookup name environment) environment)))))

; function-state-2 as described in lecture)
(define function-state-2
  (lambda (name actual-parameters environment function-state throw next)
    (bind-parameters (get-closure-parameters (lookup name environment)) actual-parameters environment function-state throw next)))

; interpret a statement in the environment with continuations for return, break, continue, throw, and "next statement"
(define interpret-statement
  (lambda (statement environment return break continue throw next current-type)
    (cond
      ((eq? 'return (statement-type statement)) (interpret-return statement environment return throw next current-type))
      ((eq? 'function (statement-type statement)) (interpret-function statement environment next current-type))
      ((eq? 'var (statement-type statement)) (interpret-declare statement environment next throw current-type))
      ((eq? '= (statement-type statement)) (interpret-assign statement environment next throw current-type))
      ((eq? 'if (statement-type statement)) (interpret-if statement environment return break continue throw next current-type))
      ((eq? 'while (statement-type statement)) (interpret-while statement environment return throw next current-type))
      ((eq? 'continue (statement-type statement)) (continue environment))
      ((eq? 'break (statement-type statement)) (break environment))
      ((eq? 'begin (statement-type statement)) (interpret-block statement environment return break continue throw next current-type))
      ((eq? 'throw (statement-type statement)) (interpret-throw statement environment throw next current-type))
      ((eq? 'try (statement-type statement)) (interpret-try statement environment return break continue throw next current-type))
      ((eq? 'funcall (statement-type statement)) (interpret-funcall (function-name-statement statement) (function-parameters-statement statement) environment return break continue throw next current-type))
      (else (myerror "Unknown statement:" (statement-type statement))))))

; returns the function's name when called as a statement
(define function-name-statement
  (lambda (statement)
  (cadr statement)))

; returns the function's list of actual-parameters when called as a statement
(define function-parameters-statement
  (lambda (statement)
    (cddr statement)
    ))

; interprets the function called as a statement, updating the environment at the end
(define interpret-funcall
  (lambda (name actual-parameters environment return break continue throw next)
    (interpret-statement-list
     (get-closure-body(lookup name environment))
     (function-state-2 name actual-parameters environment (function-state-1 name environment) throw next)
     (lambda (s v) (next (update-state environment s)))
     (lambda (s) (myerror "break outside of loop"))
     (lambda (s) (myerror "continue outside of loop"))
     (lambda (s e) (throw (update-state environment s) e))
     (lambda (s) (next (update-state environment s)))
    )
    ))

; update state method
(define update-state
  (lambda (state1 state2)
    (update-state-variables (car(variables state1)) state1 state2 (newenvironment))
     ))

; updates the variables within the state
(define update-state-variables
  (lambda (state1-vars state1 state2 state-returned)
    (cond
      ((null? state1-vars) state-returned)
      ((not (exists-in-list? (car state1-vars) (car (variables state2)))) (update-state-variables (cdr state1-vars) state1 state2 (insert (car state1-vars) (lookup (car state1-vars) state1) state-returned )))
      ((eq? (lookup (car state1-vars) state1) (lookup (car state1-vars) state2)) (update-state-variables (cdr state1-vars) state1 state2 (insert (car state1-vars) (lookup (car state1-vars) state1) state-returned )))
      (else (update-state-variables (cdr state1-vars) state1 state2 (insert (car state1-vars) (lookup (car state1-vars) state2) state-returned )))
      )))

; Calls the return continuation with the given expression value
(define interpret-return
  (lambda (statement environment return throw next current-type)
    (return environment (eval-expression (get-expr statement) environment throw next current-type))))
 
; Adds a new variable binding to the environment.  There may be an assignment with the variable
(define interpret-declare
  (lambda (statement environment next throw current-type)
    (if (exists-declare-value? statement)
        (next (insert (get-declare-var statement) (eval-expression (get-declare-value statement) environment throw next current-type) environment))
        (next (insert (get-declare-var statement) 'novalue environment)))))

; Updates the environment to add a new binding for a variable
(define interpret-assign
  (lambda (statement environment next throw current-type)
    (next (update (get-assign-lhs statement) (eval-expression (get-assign-rhs statement) environment throw next) environment))))

; We need to check if there is an else condition.  Otherwise, we evaluate the expression and do the right thing.
(define interpret-if
  (lambda (statement environment return break continue throw next current-type)
    (cond
      ((eval-expression (get-condition statement) environment throw next) (interpret-statement (get-then statement) environment return break continue throw next))
      ((exists-else? statement) (interpret-statement (get-else statement) environment return break continue throw next))
      (else (next environment)))))

; Interprets a while loop.  We must create break and continue continuations for this loop
(define interpret-while
  (lambda (statement environment return throw next current-type)
    (letrec ((loop (lambda (condition body environment)
                     (if (eval-expression condition environment throw next)
                         (interpret-statement body environment return (lambda (env) (next env)) (lambda (env) (loop condition body env)) throw (lambda (env) (loop condition body env)))
                         (next environment)))))
      (loop (get-condition statement) (get-body statement) environment))))

; Interprets a block.  The break, continue, throw and "next statement" continuations must be adjusted to pop the environment
(define interpret-block
  (lambda (statement environment return break continue throw next current-type)
    (interpret-statement-list (cdr statement)
                                         (push-frame environment)
                                         return
                                         (lambda (env) (break (pop-frame env)))
                                         (lambda (env) (continue (pop-frame env)))
                                         (lambda (v env) (throw v (pop-frame env)))
                                         (lambda (env) (next (pop-frame env))))))

; We use a continuation to throw the proper value.  Because we are not using boxes, the environment/state must be thrown as well so any environment changes will be kept
(define interpret-throw
  (lambda (statement environment throw next current-type)
    (throw (eval-expression (get-expr statement) environment throw next) environment)))

; Interpret a try-catch-finally block

; Create a continuation for the throw.  If there is no catch, it has to interpret the finally block, and once that completes throw the exception.
;   Otherwise, it interprets the catch block with the exception bound to the thrown value and interprets the finally block when the catch is done
(define create-throw-catch-continuation
  (lambda (catch-statement environment return break continue throw next finally-block current-type)
    (cond
      ((null? catch-statement) (lambda (ex env) (interpret-block finally-block env return break continue throw (lambda (env2) (throw ex env2)))))
      ((not (eq? 'catch (statement-type catch-statement))) (myerror "Incorrect catch statement"))
      (else (lambda (ex env)
                  (interpret-statement-list
                       (get-body catch-statement)
                       (insert (catch-var catch-statement) ex (push-frame env))
                       return
                       (lambda (env2) (break (pop-frame env2)))
                       (lambda (env2) (continue (pop-frame env2)))
                       (lambda (v env2) (throw v (pop-frame env2)))
                       (lambda (env2) (interpret-block finally-block (pop-frame env2) return break continue throw next))))))))

; To interpret a try block, we must adjust  the return, break, continue continuations to interpret the finally block if any of them are used.
;  We must create a new throw continuation and then interpret the try block with the new continuations followed by the finally block with the old continuations
(define interpret-try
  (lambda (statement environment return break continue throw next current-type)
    (let* ((finally-block (make-finally-block (get-finally statement)))
           (try-block (make-try-block (get-try statement)))
           (new-return (lambda (v) (interpret-block finally-block environment return break continue throw (lambda (env2) (return v)))))
           (new-break (lambda (env) (interpret-block finally-block env return break continue throw (lambda (env2) (break env2)))))
           (new-continue (lambda (env) (interpret-block finally-block env return break continue throw (lambda (env2) (continue env2)))))
           (new-throw (create-throw-catch-continuation (get-catch statement) environment return break continue throw next finally-block)))
      (interpret-block try-block environment new-return new-break new-continue new-throw (lambda (env) (interpret-block finally-block env return break continue throw next))))))

; helper methods so that I can reuse the interpret-block method on the try and finally blocks
(define make-try-block
  (lambda (try-statement)
    (cons 'begin try-statement)))

(define make-finally-block
  (lambda (finally-statement)
    (cond
      ((null? finally-statement) '(begin))
      ((not (eq? (statement-type finally-statement) 'finally)) (myerror "Incorrectly formatted finally block"))
      (else (cons 'begin (cadr finally-statement))))))

; Evaluates all possible boolean and arithmetic expressions, including constants and variables.
(define eval-expression 
  (lambda (expr environment throw next current-type)
    (cond ;(display (operand1 expr))
      ((number? expr) expr)
      ((eq? expr 'true) #t)
      ((eq? expr 'false) #f)
      ((and (contains-funcall expr) (eq? (car(operand1 expr)) 'dot)) (eval-function-expression (function-name-dot(operand1 expr)) (cddr expr) environment throw next current-type)) ;(class-name-dot (operand1 expr))
      ((not (list? expr)) (lookup expr environment))
      (else (eval-operator expr environment throw next current-type)))))

; *** gets the function name from the dot
(define function-name-dot
  (lambda (operand)
    (caddr operand)))

; *** gets the class name from teh dot
(define class-name-dot
  (lambda (operand)
    (cadr operand)))

; if the expression contains a funcall
(define contains-funcall
  (lambda (expr)
    (cond
      ((null? expr) #f)
      ((not (list? expr)) #f)
      ((eq? (car expr) 'funcall) #t)
      (else (contains-funcall(cdr expr))))))


; Evaluate a binary (or unary) operator.  Although this is not dealing with side effects, I have the routine evaluate the left operand first and then
; pass the result to eval-binary-op2 to evaluate the right operand.  This forces the operands to be evaluated in the proper order in case you choose
; to add side effects to the interpreter
(define eval-operator
  (lambda (expr environment throw next current-type)
    (cond
      ((eq? '! (operator expr)) (not (eval-expression (operand1 expr) environment throw next current-type)))
      ((and (eq? '- (operator expr)) (= 2 (length expr))) (- (eval-expression (operand1 expr) environment throw next current-type)))
      (else (eval-binary-op2 expr (eval-expression (operand1 expr) environment throw next current-type) environment throw next current-type)))))

; *** Point 9: dot included in mvalue
; Complete the evaluation of the binary operator by evaluating the second operand and performing the operation.
(define eval-binary-op2
  (lambda (expr op1value environment throw next current-type)
    (cond
      ((eq? '+ (operator expr)) (+ op1value (eval-expression (operand2 expr) environment throw next current-type)))
      ((eq? '- (operator expr)) (- op1value (eval-expression (operand2 expr) environment throw next current-type)))
      ((eq? '* (operator expr)) (* op1value (eval-expression (operand2 expr) environment throw next current-type)))
      ((eq? '/ (operator expr)) (quotient op1value (eval-expression (operand2 expr) environment throw next current-type)))
      ((eq? '% (operator expr)) (remainder op1value (eval-expression (operand2 expr) environment throw next current-type)))
      ((eq? '== (operator expr)) (isequal op1value (eval-expression (operand2 expr) environment throw next current-type)))
      ((eq? '!= (operator expr)) (not (isequal op1value (eval-expression (operand2 expr) environment throw next current-type))))
      ((eq? '< (operator expr)) (< op1value (eval-expression (operand2 expr) environment throw next current-type)))
      ((eq? '> (operator expr)) (> op1value (eval-expression (operand2 expr) environment throw next current-type)))
      ((eq? '<= (operator expr)) (<= op1value (eval-expression (operand2 expr) environment throw next current-type)))
      ((eq? '>= (operator expr)) (>= op1value (eval-expression (operand2 expr) environment throw next current-type)))
      ((eq? '|| (operator expr)) (or op1value (eval-expression (operand2 expr) environment throw next current-type)))
      ((eq? '&& (operator expr)) (and op1value (eval-expression (operand2 expr) environment throw next current-type)))
      ((eq? 'new (operator expr)) (create-instance-closure (operand1 expr) environment))
      ((eq? 'dot (operator expr)) (get-instance-value (dot-var expr) environment current-type))
      (else (myerror "Unknown operator:" (operator expr))))))

; Determines if two values are equal.  We need a special test because there are both boolean and integer types.
(define isequal
  (lambda (val1 val2)
    (if (and (number? val1) (number? val2))
        (= val1 val2)
        (eq? val1 val2))))


; **** Helper methods for lookup ***
(define dot-var
  (lambda (expr)
    ( caddr expr)))

; *** Gets the value from the class closure
(define get-instance-value
  (lambda (var environment current-type)
    (get-closure-val (get-closure-instance-values(lookup current-type environment)) (get-var-index var (get-closure-instance-names (lookup current-type environment)) 0) 0)
    ))

; *** Gets the index of the var in teh class closure
(define get-var-index
  (lambda (var names index)
    (cond
      ((null? names) 0)
      ((eq? var (car names)) index)
      ((get-var-index var (cdr names) (- 1 index)))
      )))

; *** gets the value given the index
(define get-closure-val
  (lambda (values index-target index)
    (cond
      ((eq? index-target index) (car values))
      ((get-closure-val (cdr values) index-target (+ 1 index))))))


              



;-----------------
; HELPER FUNCTIONS
;-----------------

; These helper functions define the operator and operands of a value expression
(define operator car)
(define operand1 cadr)
(define operand2 caddr)
(define operand3 cadddr)

(define exists-operand2?
  (lambda (statement)
    (not (null? (cddr statement)))))

(define exists-operand3?
  (lambda (statement)
    (not (null? (cdddr statement)))))

; these helper functions define the parts of the various statement types
(define statement-type operator)
(define get-expr operand1)
(define get-declare-var operand1)
(define get-declare-value operand2)
(define exists-declare-value? exists-operand2?)
(define get-assign-lhs operand1)
(define get-assign-rhs operand2)
(define get-condition operand1)
(define get-then operand2)
(define get-else operand3)
(define get-body operand2)
(define exists-else? exists-operand3?)
(define get-try operand1)
(define get-catch operand2)
(define get-finally operand3)

(define catch-var
  (lambda (catch-statement)
    (car (operand1 catch-statement))))


;------------------------
; Environment/State Functions
;------------------------

; create a new empty environment
(define newenvironment
  (lambda ()
    (list (newframe))))

; create an empty frame: a frame is two lists, the first are the variables and the second is the "store" of values
(define newframe
  (lambda ()
    '(() ())))

; add a frame onto the top of the environment
(define push-frame
  (lambda (environment)
    (cons (newframe) environment)))

; remove a frame from the environment
(define pop-frame
  (lambda (environment)
    (cdr environment)))

; some abstractions
(define topframe car)
(define remainingframes cdr)

; does a variable exist in the environment?
(define exists?
  (lambda (var environment)
    (cond
      ((null? environment) #f)
      ((exists-in-list? var (variables (topframe environment))) #t)
      (else (exists? var (remainingframes environment))))))

; does a variable exist in a list?
(define exists-in-list?
  (lambda (var l)
    (cond
      ((null? l) #f)
      ((eq? var (car l)) #t)
      (else (exists-in-list? var (cdr l))))))

; Looks up a value in the environment.  If the value is a boolean, it converts our languages boolean type to a Scheme boolean type
(define lookup
  (lambda (var environment)
    (lookup-variable var environment)))
 
; A helper function that does the lookup.  Returns an error if the variable does not have a legal value
(define lookup-variable
  (lambda (var environment)
    (let ((value (lookup-in-env var environment)))
      ;(if (eq? 'novalue value)
          ;(myerror "error: variable without an assigned value:" var)
          value)));)

; Return the value bound to a variable in the environment
(define lookup-in-env
  (lambda (var environment)
    (cond
      ((null? environment) (myerror "error: undefined variable" var))
      ((exists-in-list? var (variables (topframe environment))) (lookup-in-frame var (topframe environment)))
      (else (lookup-in-env var (cdr environment))))))

; Return the value bound to a variable in the frame
(define lookup-in-frame
  (lambda (var frame)
    (cond
      ((not (exists-in-list? var (variables frame))) (myerror "error: undefined variable" var))
      (else (language->scheme (get-value (indexof var (variables frame)) (store frame)))))))

; Get the location of a name in a list of names
(define indexof
  (lambda (var l)
    (cond
      ((null? l) 0)  ; should not happen
      ((eq? var (car l)) 0)
      (else (+ 1 (indexof var (cdr l)))))))

; Get the value stored at a given index in the list
(define get-value
  (lambda (n l)
    (cond
      ((zero? n) (car l))
      (else (get-value (- n 1) (cdr l))))))

; Adds a new variable/value binding pair into the environment.  Gives an error if the variable already exists in this frame.
(define insert
  (lambda (var val environment)
    (if (exists-in-list? var (variables (car environment)))
        (myerror "error: variable is being re-declared:" var)
        (cons (add-to-frame var val (car environment)) (cdr environment)))))


; Changes the binding of a variable to a new value in the environment.  Gives an error if the variable does not exist.
(define update
  (lambda (var val environment)
    (if (exists? var environment)
        (update-existing var val environment)
        (myerror "error: variable used but not defined:" var))))

; Add a new variable/value pair to the frame.
(define add-to-frame
  (lambda (var val frame)
    (list (cons var (variables frame)) (cons (scheme->language val) (store frame)))))

; Changes the binding of a variable in the environment to a new value
(define update-existing
  (lambda (var val environment)
    (if (exists-in-list? var (variables (car environment)))
        (cons (update-in-frame var val (topframe environment)) (remainingframes environment))
        (cons (topframe environment) (update-existing var val (remainingframes environment))))))

; Changes the binding of a variable in the frame to a new value.
(define update-in-frame
  (lambda (var val frame)
    (list (variables frame) (update-in-frame-store var val (variables frame) (store frame)))))

; Changes a variable binding by placing the new value in the appropriate place in the store
(define update-in-frame-store
  (lambda (var val varlist vallist)
    (cond
      ((eq? var (car varlist)) (cons (scheme->language val) (cdr vallist)))
      (else (cons (car vallist) (update-in-frame-store var val (cdr varlist) (cdr vallist)))))))

; Returns the list of variables from a frame
(define variables
  (lambda (frame)
    (car frame)))

; Returns the store from a frame
(define store
  (lambda (frame)
    (cadr frame)))


; Returns function name
(define function-name
  (lambda (statement)
    (cadr statement)))

; Returns function parameters
(define function-parameters
  (lambda (statement)
    (caddr statement)))

; Returns function body
(define function-body
  (lambda (statement)
    (cadddr statement)))
          


; Functions to convert the Scheme #t and #f to our languages true and false, and back.

(define language->scheme
  (lambda (v)
    (cond
      ((eq? v 'false) #f)
      ((eq? v 'true) #t)
      (else v))))

(define scheme->language
  (lambda (v)
    (cond
      ((eq? v #f) 'false)
      ((eq? v #t) 'true)
      (else v))))

; Because the error function is not defined in R5RS scheme, I create my own:
(define error-break (lambda (v) v))
(call-with-current-continuation (lambda (k) (set! error-break k)))

(define myerror
  (lambda (str . vals)
    (letrec ((makestr (lambda (str vals)
                        (if (null? vals)
                            str
                            (makestr (string-append str (string-append " " (symbol->string (car vals)))) (cdr vals))))))
      (error-break (display (string-append str (makestr "" vals)))))))







