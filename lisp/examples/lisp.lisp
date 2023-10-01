; A Lisp interpreter written in Lisp by MaxXing.
; Reference: The Roots of Lisp (http://www.paulgraham.com/rootsoflisp.html)

(define caar (lambda (x) (car (car x))))
(define cadr (lambda (x) (car (cdr x))))
(define cadar (lambda (x) (car (cdr (car x)))))
(define caddr (lambda (x) (car (cdr (cdr x)))))
(define caddar (lambda (x) (car (cdr (cdr (car x))))))

(define null? (lambda (x)
  (eq? x '())))

(define and (lambda (x y)
  (cond (x (cond (y 't) ('t 'f)))
        ('t 'f))))

(define or (lambda (x y)
  (cond (x 't)
        ('t (cond (y 't) ('t 'f))))))

(define not (lambda (x)
  (cond (x 'f) ('t 't))))

(define append (lambda (x y)
  (cond ((null? x) y)
        ('t (cons (car x) (append (cdr x) y))))))

(define pair (lambda (x y)
  (cond ((or (null? x) (null? y)) '())
        ('t  (cons (list (car x) (car y))
                   (pair (cdr x) (cdr y)))))))

(define assoc (lambda (x y)
  (cond ((eq? (caar y) x) (cadar y))
        ('t (assoc x (cdr y))))))

(define eval (lambda (e a)
  (cond
    ((number? e) e)
    ((atom? e) (assoc e a))
    ((atom? (car e))
     (cond
       ((eq? (car e) 'quote)    (cadr e))
       ((eq? (car e) 'atom?)    (atom? (eval (cadr e) a)))
       ((eq? (car e) 'number?)  (number? (eval (cadr e) a)))
       ((eq? (car e) 'eq?)      (eq? (eval (cadr e) a) (eval (caddr e) a)))
       ((eq? (car e) 'car)      (car (eval (cadr e) a)))
       ((eq? (car e) 'cdr)      (cdr (eval (cadr e) a)))
       ((eq? (car e) 'cons)     (cons (eval (cadr e) a) (eval (caddr e) a)))
       ((eq? (car e) 'cond)     (evcon (cdr e) a))
       ((eq? (car e) 'list)     (evlis (cdr e) a))
       ((eq? (car e) '+)        (+ (eval (cadr e) a) (eval (caddr e) a)))
       ((eq? (car e) '-)        (- (eval (cadr e) a) (eval (caddr e) a)))
       ((eq? (car e) '*)        (* (eval (cadr e) a) (eval (caddr e) a)))
       ((eq? (car e) '/)        (/ (eval (cadr e) a) (eval (caddr e) a)))
       ((eq? (car e) '>)        (> (eval (cadr e) a) (eval (caddr e) a)))
       ((eq? (car e) '<)        (< (eval (cadr e) a) (eval (caddr e) a)))
       ((eq? (car e) '>=)       (>= (eval (cadr e) a) (eval (caddr e) a)))
       ((eq? (car e) '<=)       (<= (eval (cadr e) a) (eval (caddr e) a)))
       ((eq? (car e) '=)        (= (eval (cadr e) a) (eval (caddr e) a)))
       ((eq? (car e) 'print)    (print (eval (cadr e) a)))
       ('t                      (eval (cons (assoc (car e) a) (cdr e)) a))))
    ((eq? (caar e) 'define)     (eval (cadr e)
                                      (cons (list (cadar e) (caddar e)) a)))
    ((eq? (caar e) 'lambda)     (eval (caddar e)
                                      (append (pair (cadar e) (evlis (cdr e) a))
                                              a)))
    ('t                         'error))))

(define evcon (lambda (c a)
  (cond ((eval (caar c) a)  (eval (cadar c) a))
        ('t                 (evcon (cdr c) a)))))

(define evlis (lambda (m a)
  (cond ((null? m)  '())
        ('t         (cons (eval (car m) a)
                          (evlis (cdr m) a))))))

(print
  (eval '((define map
            (lambda (f l)
              (cond ((eq? l '()) '())
                    ('t (cons (f (car l)) (map f (cdr l)))))))
          ((define fib
             (lambda (n)
               (cond ((< n 2) 1)
                     ('t (+ (fib (- n 1)) (fib (- n 2)))))))
           (map fib '(0 1 2 3 4 5 6 7 8 9))))
        '()))
