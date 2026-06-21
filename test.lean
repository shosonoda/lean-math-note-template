import Mathlib
set_option linter.style.header false --- 動作確認用のため linter オフ

#eval 1 + 1

example : 1 + 1 = 2 := by
  norm_num
