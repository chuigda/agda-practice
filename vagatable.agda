module vagatable where

data 𝕍agatable : Set where
  菜 : 𝕍agatable

data 𝔾arbage : Set where
  垃圾 : 𝔾arbage

data 𝔻epraved : Set where
  堕落 : 𝔻epraved

data 用一句话形容自己 : Set where
  总之就是菜 : 用一句话形容自己

我好_啊，我_爆了，我是什么_，我好_ : 𝕍agatable → 𝕍agatable → 𝔾arbage → 𝔻epraved → 用一句话形容自己
我好_啊，我_爆了，我是什么_，我好_ _ _ _ _ = 总之就是菜

infix 30 我好_啊，我_爆了，我是什么_，我好_

_ : 用一句话形容自己
_ = 我好 菜 啊，我 菜 爆了，我是什么 垃圾 ，我好 堕落
