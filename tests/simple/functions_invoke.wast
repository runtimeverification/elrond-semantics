;; Simple add function

func 0 :: [ i32 i32 ] -> [ i32 ]
    [ ] {
    (local.get 0)
    (local.get 1)
    (i32.add)
    (return)
}

(i32.const 7)
(i32.const 8)
(invoke 0)
#assertTopStack < i32 > 15 "invoke function 0"
#assertFunction 0 [ i32 i32 ] -> [ i32 ] [ ] "invoke function 0 exists"

;; String-named add function

func $add :: [ i32 i32 ] -> [ i32 ]
    [ ] {
    (local.get 0)
    (local.get 1)
    (i32.add)
    (return)
}

#assertFunction $add [ i32 i32 ] -> [ i32 ] [ ] "function string-named add"

;; Exported name add function

(func export $add param i32 i32 result i32
    (local.get 0)
    (local.get 1)
    (i32.add)
    (return)
)

#assertFunction $add [ i32 i32 ] -> [ i32 ] [ ] "exported function name add"

;; Remove return statement

(func 0 param i32 i32 result i32
    (local.get 0)
    (local.get 1)
    (i32.add)
)

(i32.const 7)
(i32.const 8)
(invoke 0)
#assertTopStack < i32 > 15 "invoke function 0 no return"
#assertFunction 0 [ i32 i32 ] -> [ i32 ] [ ] "invoke function 0 exists no return"

;; More complicated function with locals

(func 1 param i64 i64 i64 result i64 local i64
        (local.get 2)
          (local.get 0)
          (local.get 1)
        (i64.add)
      (i64.sub)
    (local.set 3)
    (local.get 3)
    (return)
)

(i64.const 100)
(i64.const 43)
(i64.const 22)
(invoke 0)
#assertTopStack < i64 > 35 "invoke function 1"
#assertFunction 1 [ i64 i64 i64 ] -> [ i64 ] [ i64 ] "invoke function 1 exists"

;; Function with complicated declaration of types

(func 1 local i32 result i32 param i32 i64 param i64
    (local.get 0)
    (return)
)

(i64.const 7)
(i64.const 8)
(i32.const 5)
(invoke 0)
#assertTopStack < i32 > 5 "out of order type declaration"
#assertFunction 1 [ i32 i64 i64 ] -> [ i32 ] [ i32 ] "out of order type declarations"

;; Function with empty declarations of types

(func 1 local param i64 i64 result local result i64 param
    (local.get 0)
    (return)
)

(i64.const 7)
(i64.const 8)
(invoke 0)
#assertTopStack < i64 > 8 "empty type declaration"
#assertFunction 1 [ i64 i64 ] -> [ i64 ] [ ] "empty type declarations"

;; Function with empty declarations of types, and bracketed in parentheses

(func 1 (local) (param i64 i64) (result) (local) (result i64) (param)
    (local.get 0)
    (return)
)

(i64.const 7)
(i64.const 8)
(invoke 0)
#assertTopStack < i64 > 8 "empty type declaration + parens"
#assertFunction 1 [ i64 i64 ] -> [ i64 ] [ ] "empty type declarations + parens"

;; Function with just a name

(func 3)

#assertFunction 3 [ ] -> [ ] [ ] "no domain/range or locals"

(module
    func $add :: [ i32 i32 ] -> [ i32 ]
        [ ] {
        (local.get 0)
        (local.get 1)
        (i32.add)
        (return)
    }

    func $mul :: [ i32 i32 ] -> [ i32 ]
        [ ] {
        (local.get 0)
        (local.get 1)
        (i32.mul)
        (return)
    }

    (func (export $xor) (param i32 i32) (result i32)
        (local.get 0)
        (local.get 1)
        (i32.xor)
    )
)

(i32.const 3)
(i32.const 5)
(invoke 0)
#assertTopStack < i32 > 8 "add in module correctly"

(i32.const 3)
(i32.const 5)
(invoke 1)
#assertTopStack < i32 > 15 "mul in module correctly"

(i32.const 3)
(i32.const 5)
(invoke 2)
#assertTopStack < i32 > 6 "xor in module correctly"

#assertFunction $add [ i32 i32 ] -> [ i32 ] [ ] "add function typed correctly"
#assertFunction $mul [ i32 i32 ] -> [ i32 ] [ ] "mul function typed correctly"
#assertFunction $xor [ i32 i32 ] -> [ i32 ] [ ] "xor function typed correctly"

(module
    func $f1 :: [ i32 i32 ] -> [ i32 ]
        [ i32 ] {
        (local.get 0)
        (local.get 1)
        (i32.add)
        (local.set 2)
        (local.get 0)
        (local.get 2)
        (i32.mul)
        (return)
    }

    func $f2 :: [ i32 i32 i32 ] -> [ i32 ]
        [ i32 i32 ] {
        (local.get 0)
        (local.get 2)
        (invoke 0)
        (local.get 1)
        (invoke 0)
        (local.get 0)
        (i32.mul)
        (return)
    }
)

(i32.const 3)
(i32.const 5)
(invoke 0)
(i32.const 5)
(i32.const 8)
(invoke 1)
#assertTopStack < i32 > 77000 "nested method invoke"
#assertFunction $f2 [ i32 i32 i32 ] -> [ i32 ] [ i32 i32 ] "outer invokeing method"
#assertFunction $f1 [ i32 i32     ] -> [ i32 ] [ i32     ] "inner invokeing method"

(module
    (func $dummy)

    (func $add (param i32 i32) (result i32)
        (local.get 0)
        (local.get 1)
        (i32.add)
        (return)
    )
)

#assertFunction $dummy [         ] -> [     ] [ ] "$dummy function in module"
#assertFunction $add   [ i32 i32 ] -> [ i32 ] [ ] "second function in module"