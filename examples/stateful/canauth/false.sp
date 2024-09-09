hash hmac
name k: message
fun mhash: message -> message -> message
abstract SIGN: message

channel c

process A=
 out(c, mhash(SIGN, 
