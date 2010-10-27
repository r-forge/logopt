# Code implementing different log optimal portfolio selection
# algorithms, especially linked to universal portfolios
#

require(xts)
require(quadprog)

# help routine to read one of the raw csv file, either from
# the original cover dataset or the merged sequence

read.nyse.dataset <- function (name, original = FALSE) {
	filename <- paste("../data/", ifelse(original, "NyseOld/", "NyseMerged/"), name, ".csv", sep="")
	x <- try(read.csv(filename,header=FALSE))
	# modify first column to have the full 4 digits year
	after2000 <- x[,1] < 500000
	x[,1] <- x[,1] + 19000000
	x[after2000,1] <- x[after2000,1] + 1000000
	x <- xts(x[,2], order.by=as.Date(paste(x[,1]), format="%Y%m%d"))
}

read.all.nyse.dataset <- function (original = FALSE) {
	names <- dir(paste("../data/", ifelse(original, "NyseOld/", "NyseMerged/"), sep=""), pattern=".*csv$")
	tickers <- list()	
	for (i in 1:length(names)) {
		name <- names[[i]]
		if (substr(name,1,1) == "N") next  # eliminate the csv file containing the list of ticker
		ticker <- substr(name,1,nchar(name)-4)
		tickers[[1+length(tickers)]] <- ticker 
		x <- read.nyse.dataset(ticker, original)
		if(length(tickers) == 1) { xs <- x }
		else { xs <- merge(xs, x) }
	}
	colnames(xs) <- tickers
	return(xs)
}

is.compatible <- function (b, x) {
	# b is either a vector or a matrix
	# x is n (timesteps) * m (assets)
	# we need b = 1 * m or m * 1 or n * m
	if(is.vector(b)) { return(dim(x)[2] == length(b)) }
      if(is.array(b)) { return(all(dim(b) == dim(x))) }
	return(FALSE)
}

normalize <- function (b) {
	if (is.vector(b)) { return (b/sum(b)) }
	else              { return (b/apply(b,1,sum)) }
}

w2x <- function (w) {  # this works for xts because of how lag.xts operates
  	x <- w/lag(w)
  	x[1,] <- w[1,]
  	return(x)
}

# crp and bh are very close, so we implement them as the same procedure
crp_bh <- function (b = NULL, x, bh = FALSE) {
	# bh works on w, crp on x, but otherwise they are similar
  	# - b can be either a vector (constant) or a matrix (weight at each instant in time)
  	#   if b is NULL, we use an uniform vector loading, simple reference
  	# - x is a matrix of price relative, normally an xts
	if (is.null(b)) { b <- rep(1/dim(x)[2],dim(x)[2]) }
  	if(!is.compatible(b,x)) { stop("b and x not compatible in crp(b,x)", Call.=TRUE) } 
  	b <- normalize(b)
	if (bh) { x <- cumprod(x) }
  	if (is.vector(b)) { xp <- x %*% b }
  	else              { xp <- apply(b*x, 1, sum) }
	if (bh) { return (xts(xp, order.by=index(x))) }
	else    { return (xts(cumprod(xp), order.by=index(x)))}
}

crp <- function (b = NULL, x) {
	return (crp_bh(b, x, bh = FALSE))
}

bh <- function (b = NULL, x) {
  	# we accept b as an array, even if this is not really buy and hold
	return (crp_bh(b, x, bh = TRUE))
} 

oracle <- function (x) { # non causal maximum gain
  	xp <- xts(apply(x,1,max), order.by=index(x))
  	return(xts(cumprod(xp), order.by=index(x)))
}

best.stock <- function (x) {
  	xm <- x[,which.max(cumprod(x)[dim(x)[1]])]
  	return(xts(cumprod(xm), order.by=index(x)))
}

worst.stock <- function (x) {
  	xm <- x[,which.min(cumprod(x)[dim(x)[1]])]
  	return(xts(cumprod(xm), order.by=index(x)))
}

best.envelope <- function (x) {
  	wm <- apply(cumprod(x),1,max)
  	return(xts(wm, order.by=index(x)))
}

worst.envelope <- function (x) {
  	wm <- apply(cumprod(x),1,min)
  	return(xts(wm, order.by=index(x)))
}

crp.1d <- function (x, from = 0, to = 1, n = 11) {
  # should have two columns
  if(dim(x)[2] != 2) { stop("x is not a two column series in crp.1d(b,x)", Call.=TRUE) }
  a <- seq(from, to, length.out = n)
  w.1d <- 0 * a
  t <- dim(x)[1]
  for(i in 1:n) {
      w.1d[i] <- crp(c(a[i],1-a[i]),x)[t]
  }
  return(w.1d)
}

demo.cover.ik <- function (x.ik = NULL, i.win = 2) { 
	# x.ik is supposed to be a xts containing iroquois and kinark, if NULL we read them
	# i.win is the index of the first window to use
	if (is.null(x.ik)) {
	      kinar <- read.nyse.dataset("kinar", original = TRUE)
		iroqu <- read.nyse.dataset("iroqu", original = TRUE)
		x.ik <- merge(kinar, iroqu)
  	}
      if (is.null(dev.list())) { x11() } ;
	while(length(dev.list()) < (i.win-1)) { x11() } ;
	dev.set(i.win); i.win <- i.win + 1;
	plot(index(x.ik), cumprod(x.ik[,1]), type="l", col="blue")
	lines(index(x.ik), cumprod(x.ik[,2]), col="red")
	grid() ;
	w <- crp.1d(x.ik, from=0, to=1, n=21) 
	while(length(dev.list()) < (i.win-1)) { x11() } ;
	dev.set(i.win); i.win <- i.win + 1;
	plot(w,type="l",col="blue")
	points(w, col="red", pch=19,cex=0.75)
	abline(h=sum(w)/length(w), col="green")
	grid()
}

round.to.zero <- function (b, do.round, eps) {
	if (do.round) {
		b[abs(b) < eps] <- 0
	}
	return(normalize(b))
}

bcrp.qp <- function (x, clean.up = TRUE, clean.up.eps = 1e-10 ) {
  	# use quadratic programming approximation for VERY fast results in finding best crp
  	# see the semi-log optimal article for background and solve.QP for parameters
  	Dmat <- t(x-1) %*% (x-1)
  	dvec <- apply(x-1,2,sum)
  	lb <- dim(x)[[2]]
  	Amat <- matrix(0,lb,lb+1)
  	Amat[,1] <- -1
  	for (i in 1:lb) { Amat[i,i+1] <- 1 }
  	bvec <- 0 * 1:(lb+1)
  	bvec[1] <- -1
  	b <- solve.QP(Dmat, dvec, Amat, bvec)
	return(round.to.zero(b$solution, clean.up, clean.up.eps))
}

CRPoptrescale <- function (b, x) {
  	b <- exp(b)
  	return(-crp(b,x)[dim(x)[1]])
}

bcrp.optim <- function (x, maxit=20, clean.up = TRUE, clean.up.eps = 1e-10, fast.only = FALSE ) {
  	# try to find a nice BCRP using optim (cam be slow)
  	# optim is unconstrained, and we use a trick to map any value as positive 
  	# then to remap it into the simplex, see CRPoptrescale
	if (dim(x)[1] > dim(x)[2]) {
	  	b0 <- try(bcrp.qp(x))
	}
	else {
		b0 <- rep(1,dim(x)[2])
	}
  	if (inherits(b0,"try-error")) {
		# if we cannot find the best one
		b0 <- rep(0,dim(x)[2])
      	# identify best stock and use that as start point
      	b0[which.max(apply(x,2,prod))] <- 1
		fast.only = FALSE
  	}
	if (!fast.only) {
	  	solution <- optim(b0, CRPoptrescale, gr=NULL, method="BFGS", lower=-Inf, upper=Inf,control = list(maxit=maxit), hessian=FALSE, x)
  		b0 <- exp(solution$par)
	}
	return(round.to.zero(b0/sum(b0), clean.up, clean.up.eps))
}

next.simplex.point <- function (a) {
 	# a is the current occupancy, length(a) is the number of "urns"
	# scan to find the first urn that could give a ball
	# push the ball once to the right if possible 
	# if that urn is not empty, bring the rest of the ball to urn[1]
	# returns NULL when done
	nurns <- length(a)
	for (i in 1:nurns) {
		if (a[i] > 0) {
			if (i == nurns) { return(NULL) }
			else {
				a[i+1] <- 1 + a[i+1]
				a[1] <- a[i] - 1
				if (i != 1) { a[i] <- 0 }
				return(a)
			}
		}
	}
}

count.points <- function (n, m) {
	# n urns and m balls
	a <- 0 * 1:n
	a[1] <- m
	npoints <- 0 
	repeat {
		a <- next.simplex.point(a) 
		npoints <- npoints + 1
		if (is.null(a)) { break }
	}
	return (npoints)
}

universal.cover <- function (x, n) { # should also return a vector of combined b
	m <- dim(x)[2]
	b <- 0 * 1:m
	b[1] <- n
	npts <- 0
	w <- 0 * x[,1]
	colnames[w] <- c("universal.cover")
	repeat {
		w <- w + crp(b,x)
		npts <- npts + 1
		b <- next.simplex.point(b)
		if (is.null(b)) {
			return(w/npts)
		}
	}
}

roll.bcrp <- function (x, start=1, step=1, window=NULL, fast.only=TRUE) {
      m <- dim(x)[2]
      n <- dim(x)[1]
	b <- 0 * x
	b[1:start,] <- 1/m
      i <- start+1
	if(is.null(window)) { window <- length(x) }
      b0 <-  bcrp.optim(x[max(1,i-window):(i-1)], fast.only=fast.only)
	while(i < n) {
		b0 <- bcrp.optim(x[max(1,i-window):(i-1)], fast.only=fast.only)
		b0[is.nan(b0)] <- 1/m
		j <- min(n,i+step)
		bt <- array(rep(b0,j-i+1),dim=c(m,j-i+1))
		b[i:j,] <- t(bt)
		i <- j
	}
	return(b)
} 

wscrp2 <- function (x, start=1, step=1, a=0.99, fast.only=TRUE) {
	br <- roll.bcrp (x, start, step, window=length(x), fast.only=fast.only)
	# should have different choices
      m <- dim(x)[2]
      n <- dim(x)[1]
	b <- 0 * x
	b[1:start,] <- 1/m
      i <- start+1
	b0 <- as.vector(br[i-1,])
	while(i < n) {
		b0 <- as.vector(br[i,]) * (1-a) + b0 * a
		j <- min(n,i+step)
		bt <- array(rep(b0,j-i+1),dim=c(m,j-i+1))
		b[i:j,] <- t(bt)
		i <- j
	}
	return(crp(b,x))
}

wscrp <- function (x, k0=1, k=1, a=0.99, fast.only=TRUE) {
	# exponential moving average on scrp
      m <- dim(x)[2]
      n <- dim(x)[1]
	b <- 0 * x
	b[1:k0,] <- 1/m
      i <- k0+1
      b0 <-  bcrp.optim(x[1:(i-1)], fast.only=fast.only)
	while(i < n) {
		b0 <- bcrp.optim(x[1:(i-1)], fast.only=fast.only) * (1-a) + b0 * a
		b0[is.nan(b0)] <- 1/m
		j <- min(n,i+k)
		bt <- array(rep(b0,j-i+1),dim=c(m,j-i+1))
		b[i:j,] <- t(bt)
		i <- j
	}
	return(crp(b,x))
}

scrp <- function (x, k0=1, k=1, fast.only=TRUE) { 
	return(wscrp(x, k0=k0, k=k, a=0, fast.only=fast.only)) 
}


scrp.original <- function (x, k0=1, k=1) {
	# at each t, select the bcrp for up to t-1 as the b for that t
	# for speed, this is only after a start period of K0 points (1/M before)
	# and then every K points
	m <- dim(x)[2]
      n <- dim(x)[1]
	b <- 0 * as.matrix(x)
	b[1:k0,] <- 1/m
      i <- k0+1
	while(i < n) {
		b0 <- bcrp.optim(x[1:(i-1)],fast.only=TRUE)
		j <- min(n,i+k)
		bt <- array(rep(b0,j-i+1),dim=c(m,j-i+1))
		b[i:j,] <- t(bt)
		i <- j
	}
	# there can be rows that are NaN, we replace them with 1/M
	b[is.nan(b)] <- 1/m
	return(crp(b,x))
}

