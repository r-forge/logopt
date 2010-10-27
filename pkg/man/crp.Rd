\name{crp}
\alias{crp}
\alias{bh}
\title{ Constant Balanced portfolio or Buy and Hold portfolio }
\description{
  Calculate the time evolution of either a Constant Rebalanced Portfolio
  or a Buy and Hold portfolio given the prices relative and weights.
}
\usage{
crp(b = NULL, x)
}
\usage{
bh(b = NULL, x)
}
\arguments{
  \item{b}{
    The portfolio weights with three variants: NULL, vector and time
    series of vectors.
    Null will be transformed as the uniform vector.
}
\item{x}{
          Time series of relative prices
}
}
\details{
  TBD
}
\value{
    Time series of the wealth for the portfolio.
}
\author{ Marc Delvaux }