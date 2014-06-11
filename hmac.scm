
;
; Hash-based Message Authentication Code module
; Copyright (C) 2014 Mikael More
; MIT license.
;
; Described in RFC 2104 and test vectors provided in RFC 4231.
;
; We don't provide a CRC32 HMAC for now, in lack of test vectors.
;
; ## Description of the HMAC algorithm
; The algorithm for computing a HMAC for a given key and hash algorithm follows:
;  * If the key is longer than the hash algorithm's block size, then use the hash of the key as key.
;  * Append 0x00:s to the end of the key as to align it with the hash algorithm's block size.
;  * Generate an inner key padding, which is each byte of the key XOR:ed with 0x5C. (as clarified in hmac.scm and hmac.js)
;  * Generate an outer key padding, which is each byte of the key XOR:ed with 0x36. (")
;  * The HMAC is now computed by:
;    (hash (u8vector-append outer-key-padding (hash (u8vector-append inner-key-padding message))))
;    Note that the inner hash should return binary whereas the outer according to user's choice.
;
; ## References
;  * RFC 2104: HMAC: Keyed-Hashing for Message Authentication
;    https://tools.ietf.org/html/rfc2104
;
;  * RFC 4231: Identifiers and Test Vectors for HMAC-SHA-224, HMAC-SHA-256,
;              HMAC-SHA-384, and HMAC-SHA-512
;    http://tools.ietf.org/search/rfc4231
;
;  * https://en.wikipedia.org/wiki/Hash-based_message_authentication_code#Implementation
;
;  * https://github.com/ThomasHintz/chicken-scheme-hmac/blob/master/hmac.scm
;
;  * https://code.google.com/p/crypto-js/source/browse/tags/3.1.2/src/hmac.js
;
;  * NaCL of http://nacl.cr.yp.to/install.html in crypto_auth/hmacsha256/ref/hmac.c
;
; ## TODO
;  * For elegance: The hmac-ansi-* routines are not optimally implemented, see source for notes.
;

(export hmac-u8vector
        hmac-subu8vector

        hmac-ansi-string
        hmac-ansi-substring

        hmac-string
        hmac-substring

        ; Conveniency wrappers
        ; hmac-crc32
        hmac-md5
        hmac-sha-1
        hmac-sha-224
        hmac-sha-256

        hmac-debug:actual-key&inner&outer-key-padding
        hmac-debug:test

        )

(declare (block) (standard-bindings) (extended-bindings) (fixnum))

(import digest ../misc/u8v)

; To be moved to the digest module??
(define (digest-algorithm-block-size algorithm)
  (case algorithm
    ; ((crc32  )  4) ; ?
    ((md5    ) 64) ; The value of 64 here is required to accord with the example value at
                   ; https://en.wikipedia.org/wiki/Hash-based_message_authentication_code#Examples_of_HMAC_.28MD5.2C_SHA1.2C_SHA256.29 .
    ((sha-1  ) 64) ; https://en.wikipedia.org/wiki/SHA-2#Comparison_of_SHA_functions
    ((sha-224) 64) ; "
    ((sha-256) 64) ; "
    (else       (error "Unknown algorithm" algorithm))))

(define-macro (hmac-default-result-type) ''hex)

; Uses the variables |block-size| |key-u8vect| |algorithm|
(define-macro (hmac-key&inner&outer-key-padding . code)
  `(let* (

          (key-u8vect (if (> (u8vector-length key-u8vect) block-size)
                          (digest-u8vector key-u8vect algorithm 'u8vector)
                          key-u8vect))

          (key-u8vect (u8vector-pad-to-length key-u8vect block-size))

          (inner-key-padding (u8vector-xor key-u8vect #x36))
          (outer-key-padding (u8vector-xor key-u8vect #x5C))

          )
     ,@code))

(define (hmac-debug:actual-key&inner&outer-key-padding block-size key-u8vect algorithm)
  (hmac-key&inner&outer-key-padding
   (list key-u8vect inner-key-padding outer-key-padding)))

(define (perform-hmac message message-start message-end digest-update-procedure key-u8vect algorithm result-type)

  (let* (

         (inner-digest-digest (open-digest algorithm))

         (block-size ; (/ (block-digest-width (digest-state inner-digest-digest)) 8))
                     (digest-algorithm-block-size algorithm))

         )

    (hmac-key&inner&outer-key-padding

     (let* (

            ; Simpler but slower impl:
            ; (inner-digest (digest-u8vector (u8vector-append inner-key-padding
            ;                                                 (subu8vector message message-start message-end))
            ;                                algorithm
            ;                                'u8vector
            ;                                ))

            (inner-digest
             (let ((d inner-digest-digest))

               (digest-update-subu8vector d inner-key-padding 0 block-size) ; We know inner-key-padding has the length of the block size.

               (digest-update-subu8vector d message message-start message-end)

               (close-digest d 'u8vector))) ; Return u8vector - this was clarified by the #crypto channel on FreeNode.

            ; Simpler but slower impl:
            ; (outer-digest (digest-u8vector (u8vector-append outer-key-padding
            ;                                                 inner-digest)
            ;                                algorithm
            ;                                result-type))

            (outer-digest
             (let ((d (open-digest algorithm)))

               (digest-update-subu8vector d outer-key-padding 0 block-size) ; We know inner-key-padding has the length of the block size.

               (digest-update-subu8vector d inner-digest 0 (u8vector-length inner-digest))

               (close-digest d result-type)))

            )

       outer-digest))))

(define (hmac-u8vector message-u8vect key-u8vect algorithm #!optional (result-type (hmac-default-result-type)))
  (hmac-subu8vector message-u8vect 0 (u8vector-length message-u8vect) key-u8vect algorithm result-type))

(define (hmac-subu8vector message-u8vect message-start message-end key-u8vect algorithm
                          #!optional (result-type (hmac-default-result-type))
                          )
  (perform-hmac message-u8vect message-start message-end
                digest-update-subu8vector ; = digest-update-procedure
                key-u8vect algorithm result-type))

; See the TODO for some notes.
(define (hmac-ansi-string message-ansi-string key-ansi-string algorithm  #!optional (result-type (hmac-default-result-type)))
  (hmac-ansi-substring message-ansi-string 0 (string-length message-ansi-string) key-ansi-string algorithm result-type))
(define (hmac-ansi-substring message-ansi-string message-start message-end key-ansi-string algorithm  #!optional (result-type (hmac-default-result-type)))

  ; This is a copy of |digest-ansi-substring|'s code.
  (let ((str message-ansi-string) (start message-start) (end message-end)
        (len (fx- end start)))

    (if (or (> end (string-length str))
            (> start end))

        (error "Out of range" start end)

        (let ((u8vect (make-u8vector len)))

          ; We're just absolutely sure this code is bugfree, so no need for type safety here.
          (let ()
            (declare (not safe))
            (let loop ((in-idx start) (out-idx 0))
              (if (fx< out-idx len)
                  (begin
                    (u8vector-set! u8vect out-idx (char->integer (string-ref str in-idx)))
                    (loop (fx+ in-idx 1) (fx+ out-idx 1))))))


          (perform-hmac u8vect 0 len ; message-ansi-string message-start message-end
                        digest-update-subu8vector ; = digest-update-procedure
                        (ISO-8859-1-string->u8vector key-ansi-string) ; = key-u8vect - makes sense?
                        algorithm result-type)))))

; hmac-string* is implemented in terms of |hmac-u8vector|.
(define (hmac-string message-string key-string algorithm  #!optional (result-type (hmac-default-result-type)))
  (hmac-substring message-string 0 (string-length message-string) key-string algorithm result-type))
(define (hmac-substring message-string message-start message-end key-string algorithm #!optional (result-type (hmac-default-result-type)))
  (hmac-u8vector (substring->utf8-u8vector message-string message-start message-end)
                 (string->utf8-u8vector key-string)
                 algorithm
                 result-type
                 ))

; Conveniency wrappers
(define (make-conveniency-hmac-wrapper algorithm)
  (lambda (value key #!optional start end)
    (if (string? value)

        (if start
            (hmac-substring   value start end key algorithm)
            (hmac-string      value           key algorithm))

        (if start
            (hmac-subu8vector value start end key algorithm)
            (hmac-u8vector    value           key algorithm)))))

(define hmac-crc32   (make-conveniency-hmac-wrapper 'crc32  ))
(define hmac-md5     (make-conveniency-hmac-wrapper 'md5    ))
(define hmac-sha-1   (make-conveniency-hmac-wrapper 'sha-1  ))
(define hmac-sha-224 (make-conveniency-hmac-wrapper 'sha-224))
(define hmac-sha-256 (make-conveniency-hmac-wrapper 'sha-256))


(define (hmac-debug:test)

  (define (test-hex p data key expected-result)
    (equal? (p (hex-string->u8vector data #f) (hex-string->u8vector key #f))
            expected-result))

  (and

   ; Vectors provided by https://en.wikipedia.org/wiki/Hash-based_message_authentication_code#Examples_of_HMAC_.28MD5.2C_SHA1.2C_SHA256.29 :
   (equal? (hmac-md5     "" "") "74e6f7298a9c2d168935f58c001bad88")
   (equal? (hmac-sha-1   "" "") "fbdb1d1b18aa6c08324b7d64b71fb76370690e1d")
   (equal? (hmac-sha-256 "" "") "b613679a0814d9ec772f95d778c35fc5ff1697c493715653c6c712144292c5ad")

   (equal? (hmac-md5     "The quick brown fox jumps over the lazy dog" "key") "80070713463e7749b90c2dc24911e275")
   (equal? (hmac-sha-1   "The quick brown fox jumps over the lazy dog" "key") "de7c9b85b8b78aa6bc8a7a36f70a90701c9db4d9")
   (equal? (hmac-sha-256 "The quick brown fox jumps over the lazy dog" "key") "f7bc83f430538424b13298e6aa6fb143ef4d59a14946175997479dbc2d1a3cd8")
   
   ; Test vectors from RFC 4231
   ; Test case 1, data is "Hi There"
   (test-hex hmac-sha-224 "4869205468657265" "0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b" "896fb1128abbdf196832107cd49df33f47b4b1169912ba4f53684b22"        )
   (test-hex hmac-sha-256 "4869205468657265" "0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b" "b0344c61d8db38535ca8afceaf0bf12b881dc200c9833da726e9376c2e32cff7")
   ; Test case 2, key = "Jefe" and data = "what do ya want for nothing?"
   (test-hex hmac-sha-224 "7768617420646f2079612077616e7420666f72206e6f7468696e673f" "4a656665" "a30e01098bc6dbbf45690f3a7e9e6d0f8bbea2a39e6148008fd05e44"        )
   (test-hex hmac-sha-256 "7768617420646f2079612077616e7420666f72206e6f7468696e673f" "4a656665" "5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843")
   ; Test case 3
   (test-hex hmac-sha-224 "dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd" "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa" "7fb3cb3588c6c1f6ffa9694d7d6ad2649365b0c1f65d69d1ec8333ea"        )
   (test-hex hmac-sha-256 "dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd" "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa" "773ea91e36800e46854db8ebd09181a72959098b3ef8c122d9635514ced565fe")
   ; Test case 4
   (test-hex hmac-sha-224 "cdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcd" "0102030405060708090a0b0c0d0e0f10111213141516171819" "6c11506874013cac6a2abc1bb382627cec6a90d86efc012de7afec5a"        )
   (test-hex hmac-sha-256 "cdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcd" "0102030405060708090a0b0c0d0e0f10111213141516171819" "82558a389a443c0ea4cc819899f2083a85f0faa3e578f8077a2e3ff46729665b")
   ; Test case 5 is about truncation and we don't do that, so we skip that one.
   ; Test case 6
   (test-hex hmac-sha-224 "54657374205573696e67204c6172676572205468616e20426c6f636b2d53697a65204b6579202d2048617368204b6579204669727374" "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa" "95e9a0db962095adaebe9b2d6f0dbce2d499f112f2d2b7273fa6870e"        )
   (test-hex hmac-sha-256 "54657374205573696e67204c6172676572205468616e20426c6f636b2d53697a65204b6579202d2048617368204b6579204669727374" "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa" "60e431591ee0b67f0d8a26aacbf5b77f8e0bc6213728c5140546040f0ee37f54")
   ; Test case 7
   (test-hex hmac-sha-224 "5468697320697320612074657374207573696e672061206c6172676572207468616e20626c6f636b2d73697a65206b657920616e642061206c6172676572207468616e20626c6f636b2d73697a6520646174612e20546865206b6579206e6565647320746f20626520686173686564206265666f7265206265696e6720757365642062792074686520484d414320616c676f726974686d2e" "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa" "3a854166ac5d9f023f54d517d0b39dbd946770db9c2b95c9f6f565d1"        )
   (test-hex hmac-sha-256 "5468697320697320612074657374207573696e672061206c6172676572207468616e20626c6f636b2d73697a65206b657920616e642061206c6172676572207468616e20626c6f636b2d73697a6520646174612e20546865206b6579206e6565647320746f20626520686173686564206265666f7265206265696e6720757365642062792074686520484d414320616c676f726974686d2e" "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa" "9b09ffa71b942fcb27635fbcd5b0e944bfdc63644f0713938a7f51535c3a35e2")

   ; Double-checked using http://myeasywww.appspot.com/utility/free/online/Crypt_Decrypt-MD5-AES-HMAC-SHA-DES-RABBIT/en?command=UTILITY&ID=2
   ; and https://quickhash.com/ :
   (equal? (hmac-md5     "Awesomeness." "This string is longer than sixty-four characters, just so you know.") "c11692f0b7fc62a76f538e0fe86fb2bb")
   (equal? (hmac-sha-1   "Awesomeness." "This string is longer than sixty-four characters, just so you know.") "e2af15ee298e5b7ecc400c9f938c69ba4747b53c")
   (equal? (hmac-sha-256 "Awesomeness." "This string is longer than sixty-four characters, just so you know.") "e2315eea89ab6598d8b2698a56eef77c997900d7e46a02e877666323fe7e23cd")

   ; Double-checked using https://quickhash.com/ :
   ; (equal? (hmac-crc32   "Awesomeness." "This string is longer than sixty-four characters, just so you know.") "9bab1f86")

   ))

