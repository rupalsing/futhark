-- ==
-- input { [1,2,3,4] 2 42 } output { [1i32, 2i32, 42i32, 4i32] }
-- structure { Replicate 0 Assert 1 }

let main (xs: *[]i32) (i: i32) (v: i32) =
  xs with [i:i+1] = replicate 1 v
