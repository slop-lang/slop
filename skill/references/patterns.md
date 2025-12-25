# SLOP Patterns Reference

## Arena Allocation

Standard pattern for request-scoped memory:

```
(fn handle-request ((req (Ptr Request)))
  (@intent "Process incoming request")
  (@spec (((Ptr Request)) -> (Ptr Response)))
  
  (with-arena 4096
    (let ((user (parse-user arena req))
          (result (process arena user)))
      (send-response result))))
; Arena freed automatically at end
```

For functions that allocate:

```
(fn create-user ((arena Arena) (name String) (email String))
  (@intent "Create a new user")
  (@spec ((Arena String String) -> (Ptr User)))
  (@alloc arena)
  
  (let ((user (arena-alloc arena (sizeof User))))
    (set! user name name)
    (set! user email email)
    user))
```

## Error Handling

### Result Pattern

```
(fn read-file ((arena Arena) (path String))
  (@intent "Read file contents")
  (@spec ((Arena String) -> (Result (Ptr Bytes) IoError)))
  (@alloc arena)
  
  (let ((fd (open path)))
    (if (< fd 0)
      (error 'file-not-found)
      (let ((data (read-all arena fd)))
        (close fd)
        (ok data)))))
```

### Matching Results

```
(fn process ((arena Arena) (path String))
  (match (read-file arena path)
    ((ok data) 
      (parse arena data))
    ((error 'file-not-found)
      (error 'missing-input))
    ((error e)
      (error e))))
```

### Early Return with ?

```
(fn process-all ((arena Arena) (paths (List String)))
  (@spec ((Arena (List String)) -> (Result (List Data) Error)))
  
  (let ((results (list-new arena 10)))
    (for-each (path paths)
      ;; ? returns early on error
      (let ((data (? (read-file arena path))))
        (list-push arena results data)))
    (ok results)))
```

## Iterating Collections

### For-Each

```
(fn sum-ages ((users (Ptr (List (Ptr User)))))
  (@intent "Sum all user ages")
  (@spec (((Ptr (List (Ptr User)))) -> Int))
  (@pure)
  
  (let ((total 0))
    (for-each (user users)
      (when (. user age)
        (set! total (+ total (. (. user age) value)))))
    total))
```

### For Range

```
(fn fill-zeros ((arr (Ptr (Array Int 100))))
  (for (i 0 100)
    (set! (@ arr i) 0)))
```

### While

```
(fn find-first ((list (Ptr (List Int))) (pred (Fn (Int) -> Bool)))
  (@spec (((Ptr (List Int)) (Fn (Int) -> Bool)) -> (Option Int)))
  
  (let ((i 0)
        (len (. list len)))
    (while (< i len)
      (let ((val (@ (. list data) i)))
        (if (pred val)
          (return (some val))
          (set! i (+ i 1)))))
    (none)))
```

## Validation Pattern

```
(fn validate-user ((input (Ptr CreateUserInput)))
  (@intent "Validate user input")
  (@spec (((Ptr CreateUserInput)) -> (Result Unit ValidationError)))
  (@pure)
  
  (cond
    ((< (string-len (. input email)) 5)
      (error 'email-too-short))
    ((< (string-len (. input password)) 8)
      (error 'password-too-short))
    ((not (contains (. input email) "@"))
      (error 'invalid-email))
    (else
      (ok unit))))
```

## Builder Pattern

```
(type RequestBuilder (record
  (arena Arena)
  (method Method)
  (url String)
  (headers (Ptr (List Header)))
  (body (Option (Ptr Bytes)))))

(fn request-new ((arena Arena))
  (@spec ((Arena) -> (Ptr RequestBuilder)))
  (let ((b (arena-alloc arena (sizeof RequestBuilder))))
    (set! b arena arena)
    (set! b method 'GET)
    (set! b headers (list-new arena 8))
    b))

(fn request-method ((b (Ptr RequestBuilder)) (m Method))
  (@spec (((Ptr RequestBuilder) Method) -> (Ptr RequestBuilder)))
  (set! b method m)
  b)

(fn request-url ((b (Ptr RequestBuilder)) (u String))
  (@spec (((Ptr RequestBuilder) String) -> (Ptr RequestBuilder)))
  (set! b url u)
  b)

(fn request-build ((b (Ptr RequestBuilder)))
  (@spec (((Ptr RequestBuilder)) -> (Ptr Request)))
  ;; Convert builder to immutable request
  ...)
```

## State Machine

```
(type ConnState (enum
  disconnected
  connecting
  connected
  closing))

(type Connection (record
  (state ConnState)
  (socket (Option Socket))
  (buffer (Ptr Bytes))))

(fn conn-transition ((conn (Ptr Connection)) (event Event))
  (@intent "Handle state transition")
  (@spec (((Ptr Connection) Event) -> (Result Unit ConnError)))
  
  (match (tuple (. conn state) event)
    ;; disconnected + connect → connecting
    (((quote disconnected) (quote connect))
      (set! conn state 'connecting)
      (ok unit))
    
    ;; connecting + connected → connected
    (((quote connecting) (quote connected sock))
      (set! conn state 'connected)
      (set! conn socket (some sock))
      (ok unit))
    
    ;; connected + close → closing
    (((quote connected) (quote close))
      (set! conn state 'closing)
      (ok unit))
    
    ;; Invalid transition
    (else
      (error 'invalid-transition))))
```

## Resource Cleanup

```
(fn with-file ((path String) (mode FileMode) (body (Fn (File) -> T)))
  (@intent "Execute body with open file, ensure cleanup")
  (@spec ((String FileMode (Fn (File) -> T)) -> (Result T IoError)))
  
  (let ((file (? (file-open path mode))))
    (let ((result (body file)))
      (file-close file)
      (ok result))))

;; Usage
(with-file "data.txt" 'read (fn (f)
  (file-read-all arena f)))
```

## FFI Pattern

```
;; Declare external C function
(ffi-import "openssl/sha.h"
  (SHA256 ((data (Ptr U8)) (len U64) (out (Ptr U8))) (Ptr U8)))

;; Wrap with SLOP types
(fn hash-sha256 ((arena Arena) (data Bytes))
  (@intent "Compute SHA256 hash")
  (@spec ((Arena Bytes) -> Bytes))
  (@alloc arena)
  
  (let ((out (arena-alloc arena 32)))
    (SHA256 (. data ptr) (. data len) out)
    (bytes-from-ptr out 32)))
```
