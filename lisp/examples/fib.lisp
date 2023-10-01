(define null?
  (lambda (l) (eq? l '())))

(define map
  (lambda (f l)
    (cond ((null? l) '())
          ('t (cons (f (car l)) (map f (cdr l)))))))

(define fib
  (lambda (n)
    (cond ((< n 2) 1)
          ('t (+ (fib (- n 1)) (fib (- n 2)))))))

(define range
  (lambda (a b)
    (cond ((< a b) (cons a (range (+ a 1) b)))
          ('t '()))))

(print (map fib (range 0 20)))
