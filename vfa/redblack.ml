
type key = int

type color =
| Red
| Black

type 'v tree =
| E
| T of color * 'v tree * key * 'v * 'v tree

(** val empty_tree : 'a1 tree **)

let empty_tree =
  E

(** val lookup : 'a1 -> key -> 'a1 tree -> 'a1 **)

let rec lookup d x = function
| E -> d
| T (_, tl, k, v, tr) ->
  if ( < ) x k then lookup d x tl else if ( < ) k x then lookup d x tr else v

(** val make_black : 'a1 tree -> 'a1 tree **)

let make_black = function
| E -> E
| T (_, a, x, vx, b) -> T (Black, a, x, vx, b)

(** val balance : color -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree **)

let balance c t1 k vk t2 =
  match c with
  | Red -> T (Red, t1, k, vk, t2)
  | Black ->
    (match t1 with
     | E ->
       (match t2 with
        | E -> T (Black, t1, k, vk, t2)
        | T (c0, b, y, vy, d) ->
          (match c0 with
           | Red ->
             (match b with
              | E ->
                (match d with
                 | E -> T (Black, t1, k, vk, t2)
                 | T (c1, c2, z, vz, d0) ->
                   (match c1 with
                    | Red ->
                      (match t1 with
                       | E ->
                         T (Black, (T (Red, t1, k, vk, b)), y, vy, (T (Red,
                           c2, z, vz, d0)))
                       | T (c3, _, _, _, _) ->
                         (match c3 with
                          | Red ->
                            T (Red, (make_black t1), k, vk, (make_black t2))
                          | Black ->
                            T (Black, (T (Red, t1, k, vk, b)), y, vy, (T
                              (Red, c2, z, vz, d0)))))
                    | Black -> T (Black, t1, k, vk, t2)))
              | T (c1, b0, y0, vy0, c2) ->
                (match c1 with
                 | Red ->
                   (match t1 with
                    | E ->
                      T (Black, (T (Red, t1, k, vk, b0)), y0, vy0, (T (Red,
                        c2, y, vy, d)))
                    | T (c3, _, _, _, _) ->
                      (match c3 with
                       | Red ->
                         T (Red, (make_black t1), k, vk, (make_black t2))
                       | Black ->
                         T (Black, (T (Red, t1, k, vk, b0)), y0, vy0, (T
                           (Red, c2, y, vy, d)))))
                 | Black ->
                   (match d with
                    | E -> T (Black, t1, k, vk, t2)
                    | T (c3, c4, z, vz, d0) ->
                      (match c3 with
                       | Red ->
                         (match t1 with
                          | E ->
                            T (Black, (T (Red, t1, k, vk, b)), y, vy, (T
                              (Red, c4, z, vz, d0)))
                          | T (c5, _, _, _, _) ->
                            (match c5 with
                             | Red ->
                               T (Red, (make_black t1), k, vk,
                                 (make_black t2))
                             | Black ->
                               T (Black, (T (Red, t1, k, vk, b)), y, vy, (T
                                 (Red, c4, z, vz, d0)))))
                       | Black -> T (Black, t1, k, vk, t2)))))
           | Black -> T (Black, t1, k, vk, t2)))
     | T (c0, a, x, vx, c1) ->
       (match c0 with
        | Red ->
          (match a with
           | E ->
             (match c1 with
              | E ->
                (match t2 with
                 | E -> T (Black, t1, k, vk, t2)
                 | T (c2, b, y, vy, d) ->
                   (match c2 with
                    | Red ->
                      (match b with
                       | E ->
                         (match d with
                          | E -> T (Black, t1, k, vk, t2)
                          | T (c3, c4, z, vz, d0) ->
                            (match c3 with
                             | Red ->
                               (match t1 with
                                | E ->
                                  T (Black, (T (Red, t1, k, vk, b)), y, vy,
                                    (T (Red, c4, z, vz, d0)))
                                | T (c5, _, _, _, _) ->
                                  (match c5 with
                                   | Red ->
                                     T (Red, (make_black t1), k, vk,
                                       (make_black t2))
                                   | Black ->
                                     T (Black, (T (Red, t1, k, vk, b)), y,
                                       vy, (T (Red, c4, z, vz, d0)))))
                             | Black -> T (Black, t1, k, vk, t2)))
                       | T (c3, b0, y0, vy0, c4) ->
                         (match c3 with
                          | Red ->
                            (match t1 with
                             | E ->
                               T (Black, (T (Red, t1, k, vk, b0)), y0, vy0,
                                 (T (Red, c4, y, vy, d)))
                             | T (c5, _, _, _, _) ->
                               (match c5 with
                                | Red ->
                                  T (Red, (make_black t1), k, vk,
                                    (make_black t2))
                                | Black ->
                                  T (Black, (T (Red, t1, k, vk, b0)), y0,
                                    vy0, (T (Red, c4, y, vy, d)))))
                          | Black ->
                            (match d with
                             | E -> T (Black, t1, k, vk, t2)
                             | T (c5, c6, z, vz, d0) ->
                               (match c5 with
                                | Red ->
                                  (match t1 with
                                   | E ->
                                     T (Black, (T (Red, t1, k, vk, b)), y,
                                       vy, (T (Red, c6, z, vz, d0)))
                                   | T (c7, _, _, _, _) ->
                                     (match c7 with
                                      | Red ->
                                        T (Red, (make_black t1), k, vk,
                                          (make_black t2))
                                      | Black ->
                                        T (Black, (T (Red, t1, k, vk, b)), y,
                                          vy, (T (Red, c6, z, vz, d0)))))
                                | Black -> T (Black, t1, k, vk, t2)))))
                    | Black -> T (Black, t1, k, vk, t2)))
              | T (c2, b, y, vy, c3) ->
                (match c2 with
                 | Red ->
                   (match t2 with
                    | E ->
                      T (Black, (T (Red, a, x, vx, b)), y, vy, (T (Red, c3,
                        k, vk, t2)))
                    | T (c4, _, _, _, _) ->
                      (match c4 with
                       | Red ->
                         T (Red, (make_black t1), k, vk, (make_black t2))
                       | Black ->
                         T (Black, (T (Red, a, x, vx, b)), y, vy, (T (Red,
                           c3, k, vk, t2)))))
                 | Black ->
                   (match t2 with
                    | E -> T (Black, t1, k, vk, t2)
                    | T (c4, b0, y0, vy0, d) ->
                      (match c4 with
                       | Red ->
                         (match b0 with
                          | E ->
                            (match d with
                             | E -> T (Black, t1, k, vk, t2)
                             | T (c5, c6, z, vz, d0) ->
                               (match c5 with
                                | Red ->
                                  (match t1 with
                                   | E ->
                                     T (Black, (T (Red, t1, k, vk, b0)), y0,
                                       vy0, (T (Red, c6, z, vz, d0)))
                                   | T (c7, _, _, _, _) ->
                                     (match c7 with
                                      | Red ->
                                        T (Red, (make_black t1), k, vk,
                                          (make_black t2))
                                      | Black ->
                                        T (Black, (T (Red, t1, k, vk, b0)),
                                          y0, vy0, (T (Red, c6, z, vz, d0)))))
                                | Black -> T (Black, t1, k, vk, t2)))
                          | T (c5, b1, y1, vy1, c6) ->
                            (match c5 with
                             | Red ->
                               (match t1 with
                                | E ->
                                  T (Black, (T (Red, t1, k, vk, b1)), y1,
                                    vy1, (T (Red, c6, y0, vy0, d)))
                                | T (c7, _, _, _, _) ->
                                  (match c7 with
                                   | Red ->
                                     T (Red, (make_black t1), k, vk,
                                       (make_black t2))
                                   | Black ->
                                     T (Black, (T (Red, t1, k, vk, b1)), y1,
                                       vy1, (T (Red, c6, y0, vy0, d)))))
                             | Black ->
                               (match d with
                                | E -> T (Black, t1, k, vk, t2)
                                | T (c7, c8, z, vz, d0) ->
                                  (match c7 with
                                   | Red ->
                                     (match t1 with
                                      | E ->
                                        T (Black, (T (Red, t1, k, vk, b0)),
                                          y0, vy0, (T (Red, c8, z, vz, d0)))
                                      | T (c9, _, _, _, _) ->
                                        (match c9 with
                                         | Red ->
                                           T (Red, (make_black t1), k, vk,
                                             (make_black t2))
                                         | Black ->
                                           T (Black, (T (Red, t1, k, vk,
                                             b0)), y0, vy0, (T (Red, c8, z,
                                             vz, d0)))))
                                   | Black -> T (Black, t1, k, vk, t2)))))
                       | Black -> T (Black, t1, k, vk, t2)))))
           | T (c2, a0, x0, vx0, b) ->
             (match c2 with
              | Red ->
                (match t2 with
                 | E ->
                   T (Black, (T (Red, a0, x0, vx0, b)), x, vx, (T (Red, c1,
                     k, vk, t2)))
                 | T (c3, _, _, _, _) ->
                   (match c3 with
                    | Red -> T (Red, (make_black t1), k, vk, (make_black t2))
                    | Black ->
                      T (Black, (T (Red, a0, x0, vx0, b)), x, vx, (T (Red,
                        c1, k, vk, t2)))))
              | Black ->
                (match c1 with
                 | E ->
                   (match t2 with
                    | E -> T (Black, t1, k, vk, t2)
                    | T (c3, b0, y, vy, d) ->
                      (match c3 with
                       | Red ->
                         (match b0 with
                          | E ->
                            (match d with
                             | E -> T (Black, t1, k, vk, t2)
                             | T (c4, c5, z, vz, d0) ->
                               (match c4 with
                                | Red ->
                                  (match t1 with
                                   | E ->
                                     T (Black, (T (Red, t1, k, vk, b0)), y,
                                       vy, (T (Red, c5, z, vz, d0)))
                                   | T (c6, _, _, _, _) ->
                                     (match c6 with
                                      | Red ->
                                        T (Red, (make_black t1), k, vk,
                                          (make_black t2))
                                      | Black ->
                                        T (Black, (T (Red, t1, k, vk, b0)),
                                          y, vy, (T (Red, c5, z, vz, d0)))))
                                | Black -> T (Black, t1, k, vk, t2)))
                          | T (c4, b1, y0, vy0, c5) ->
                            (match c4 with
                             | Red ->
                               (match t1 with
                                | E ->
                                  T (Black, (T (Red, t1, k, vk, b1)), y0,
                                    vy0, (T (Red, c5, y, vy, d)))
                                | T (c6, _, _, _, _) ->
                                  (match c6 with
                                   | Red ->
                                     T (Red, (make_black t1), k, vk,
                                       (make_black t2))
                                   | Black ->
                                     T (Black, (T (Red, t1, k, vk, b1)), y0,
                                       vy0, (T (Red, c5, y, vy, d)))))
                             | Black ->
                               (match d with
                                | E -> T (Black, t1, k, vk, t2)
                                | T (c6, c7, z, vz, d0) ->
                                  (match c6 with
                                   | Red ->
                                     (match t1 with
                                      | E ->
                                        T (Black, (T (Red, t1, k, vk, b0)),
                                          y, vy, (T (Red, c7, z, vz, d0)))
                                      | T (c8, _, _, _, _) ->
                                        (match c8 with
                                         | Red ->
                                           T (Red, (make_black t1), k, vk,
                                             (make_black t2))
                                         | Black ->
                                           T (Black, (T (Red, t1, k, vk,
                                             b0)), y, vy, (T (Red, c7, z, vz,
                                             d0)))))
                                   | Black -> T (Black, t1, k, vk, t2)))))
                       | Black -> T (Black, t1, k, vk, t2)))
                 | T (c3, b0, y, vy, c4) ->
                   (match c3 with
                    | Red ->
                      (match t2 with
                       | E ->
                         T (Black, (T (Red, a, x, vx, b0)), y, vy, (T (Red,
                           c4, k, vk, t2)))
                       | T (c5, _, _, _, _) ->
                         (match c5 with
                          | Red ->
                            T (Red, (make_black t1), k, vk, (make_black t2))
                          | Black ->
                            T (Black, (T (Red, a, x, vx, b0)), y, vy, (T
                              (Red, c4, k, vk, t2)))))
                    | Black ->
                      (match t2 with
                       | E -> T (Black, t1, k, vk, t2)
                       | T (c5, b1, y0, vy0, d) ->
                         (match c5 with
                          | Red ->
                            (match b1 with
                             | E ->
                               (match d with
                                | E -> T (Black, t1, k, vk, t2)
                                | T (c6, c7, z, vz, d0) ->
                                  (match c6 with
                                   | Red ->
                                     (match t1 with
                                      | E ->
                                        T (Black, (T (Red, t1, k, vk, b1)),
                                          y0, vy0, (T (Red, c7, z, vz, d0)))
                                      | T (c8, _, _, _, _) ->
                                        (match c8 with
                                         | Red ->
                                           T (Red, (make_black t1), k, vk,
                                             (make_black t2))
                                         | Black ->
                                           T (Black, (T (Red, t1, k, vk,
                                             b1)), y0, vy0, (T (Red, c7, z,
                                             vz, d0)))))
                                   | Black -> T (Black, t1, k, vk, t2)))
                             | T (c6, b2, y1, vy1, c7) ->
                               (match c6 with
                                | Red ->
                                  (match t1 with
                                   | E ->
                                     T (Black, (T (Red, t1, k, vk, b2)), y1,
                                       vy1, (T (Red, c7, y0, vy0, d)))
                                   | T (c8, _, _, _, _) ->
                                     (match c8 with
                                      | Red ->
                                        T (Red, (make_black t1), k, vk,
                                          (make_black t2))
                                      | Black ->
                                        T (Black, (T (Red, t1, k, vk, b2)),
                                          y1, vy1, (T (Red, c7, y0, vy0, d)))))
                                | Black ->
                                  (match d with
                                   | E -> T (Black, t1, k, vk, t2)
                                   | T (c8, c9, z, vz, d0) ->
                                     (match c8 with
                                      | Red ->
                                        (match t1 with
                                         | E ->
                                           T (Black, (T (Red, t1, k, vk,
                                             b1)), y0, vy0, (T (Red, c9, z,
                                             vz, d0)))
                                         | T (c10, _, _, _, _) ->
                                           (match c10 with
                                            | Red ->
                                              T (Red, (make_black t1), k, vk,
                                                (make_black t2))
                                            | Black ->
                                              T (Black, (T (Red, t1, k, vk,
                                                b1)), y0, vy0, (T (Red, c9,
                                                z, vz, d0)))))
                                      | Black -> T (Black, t1, k, vk, t2)))))
                          | Black -> T (Black, t1, k, vk, t2)))))))
        | Black ->
          (match t2 with
           | E -> T (Black, t1, k, vk, t2)
           | T (c2, b, y, vy, d) ->
             (match c2 with
              | Red ->
                (match b with
                 | E ->
                   (match d with
                    | E -> T (Black, t1, k, vk, t2)
                    | T (c3, c4, z, vz, d0) ->
                      (match c3 with
                       | Red ->
                         (match t1 with
                          | E ->
                            T (Black, (T (Red, t1, k, vk, b)), y, vy, (T
                              (Red, c4, z, vz, d0)))
                          | T (c5, _, _, _, _) ->
                            (match c5 with
                             | Red ->
                               T (Red, (make_black t1), k, vk,
                                 (make_black t2))
                             | Black ->
                               T (Black, (T (Red, t1, k, vk, b)), y, vy, (T
                                 (Red, c4, z, vz, d0)))))
                       | Black -> T (Black, t1, k, vk, t2)))
                 | T (c3, b0, y0, vy0, c4) ->
                   (match c3 with
                    | Red ->
                      (match t1 with
                       | E ->
                         T (Black, (T (Red, t1, k, vk, b0)), y0, vy0, (T
                           (Red, c4, y, vy, d)))
                       | T (c5, _, _, _, _) ->
                         (match c5 with
                          | Red ->
                            T (Red, (make_black t1), k, vk, (make_black t2))
                          | Black ->
                            T (Black, (T (Red, t1, k, vk, b0)), y0, vy0, (T
                              (Red, c4, y, vy, d)))))
                    | Black ->
                      (match d with
                       | E -> T (Black, t1, k, vk, t2)
                       | T (c5, c6, z, vz, d0) ->
                         (match c5 with
                          | Red ->
                            (match t1 with
                             | E ->
                               T (Black, (T (Red, t1, k, vk, b)), y, vy, (T
                                 (Red, c6, z, vz, d0)))
                             | T (c7, _, _, _, _) ->
                               (match c7 with
                                | Red ->
                                  T (Red, (make_black t1), k, vk,
                                    (make_black t2))
                                | Black ->
                                  T (Black, (T (Red, t1, k, vk, b)), y, vy,
                                    (T (Red, c6, z, vz, d0)))))
                          | Black -> T (Black, t1, k, vk, t2)))))
              | Black -> T (Black, t1, k, vk, t2)))))

(** val ins : key -> 'a1 -> 'a1 tree -> 'a1 tree **)

let rec ins x vx = function
| E -> T (Red, E, x, vx, E)
| T (c, a, y, vy, b) ->
  if ( < ) x y
  then balance c (ins x vx a) y vy b
  else if ( < ) y x then balance c a y vy (ins x vx b) else T (c, a, x, vx, b)

(** val insert : key -> 'a1 -> 'a1 tree -> 'a1 tree **)

let insert x vx t =
  make_black (ins x vx t)

(** val elements_aux : 'a1 tree -> (key * 'a1) list -> (key * 'a1) list **)

let rec elements_aux t acc =
  match t with
  | E -> acc
  | T (_, l, k, v, r) -> elements_aux l ((k , v)::(elements_aux r acc))

(** val elements : 'a1 tree -> (key * 'a1) list **)

let elements t =
  elements_aux t []
