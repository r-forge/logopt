\name{bh}
\alias{bh}
\title{Buy and Hold portfolio}
\description{
  Calculate the time evolution of a Buy and Hold portfolio wealth given the prices relative and weights.
}
\usage{
bh(x, b = NULL)
}
\arguments{
\item{x}{ Time series of relative prices }
\item{b}{ The portfolio weights with two variants: NULL or a vector.
NULL will be transformed as the uniform vector.
}
}
\details{
  Calculate the time series of prices for the underlying assets, then calculate the wealth as a weighted sum of the individual assets.
}
\value{
    Time series of the wealth for the portfolio.
}
\examples{
require(logopt)
data(nyse.cover.1962.1984)
w <- bh(nyse.cover.1962.1984)
plot(w, type="l", color="blue")
}  \author{ Marc Delvaux }