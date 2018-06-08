module T where

class F a where
class F a => A a where
class A a => M a where

class AM a where

class morphism AM -> M where
