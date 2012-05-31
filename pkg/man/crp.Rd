\name{crp}
\alias{crp}
\title{Constant Rebalanced portfolio}
\description{
  Calculate the time evolution of a Constant Rebalanced Portfolio wealth
  given the prices relative and weights.
}
\usage{
crp(x, b = NULL)
}
\arguments{
\item{x}{ Time series of relative prices }
\item{b}{ The portfolio weights with three variants: NULL, vector and time
series of vectors.
NULL will be transformed as the uniform vector.
}
}
\details{
  Calculate the relative wealth increase of the portfolio as the weigthed sum
  of the price relatives of the individual set, then calculate the time
  series of the portfolio wealth as the cumprod.
}
\value{
    Time series of the wealth for the portfolio.
}
\examples{
require(logopt)
data(nyse.cover.1962.1984)
w <- crp(nyse.cover.1962.1984)
plot(w, type="l", color="blue")
}  
\author{ Marc Delvaux }